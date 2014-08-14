elabDescription :: [Int] -> Name -> PTerm ->
                   [(Docstring, [(Name, Docstring)], Name, PTerm, FC, [Name])] ->
                   ElabInfo -> Idris ()
elabDescription paramPos dn ty cons info = do
  elabDecl EAll toplevel labelsTyDecl
  elabDecl EAll toplevel labelsClauses
  elabDecl EAll toplevel descTyDecl
  elabDecl EAll toplevel descClauses
  elabDecl EAll toplevel aliasTyDecl
  elabDecl EAll toplevel aliasClauses
  mapM_ (elabDecl EAll toplevel) aliasCnssTyDecl
  mapM_ (elabDecl EAll toplevel) aliasCnssClauses
  where labelsTy :: PTerm
        labelsTy = PRef emptyFC (sNS (sUN "CEnum") ["Generic", "Prelude"])
        labelsName :: Name
        labelsName = SN . LabelsN $ dn
        labelsTyDecl :: PDecl
        labelsTyDecl = PTy emptyDocstring [] defaultSyntax emptyFC [TotalFn] labelsName labelsTy
        -- Extract names from constructors and map them to Idris lists
        labelsClauses :: PDecl
        labelsClauses = 
          PClauses emptyFC [TotalFn] labelsName 
             [PClause emptyFC labelsName (PRef emptyFC labelsName) [] 
               (mkList emptyFC (map (\(doc, adocs, cnm, cty, cfc, cargs)
                   -> PConstant . Str . show $ cnm) cons)) []]
        descName :: Name
        descName = SN . DescN $ dn
        descTy :: PTerm -> PTerm
        descTy indexType = 
           PApp emptyFC (PRef emptyFC (sNS (sUN "TaggedDesc") ["Generic", "Prelude"]))
             [pexp $ PRef emptyFC labelsName, pexp natZ, pexp indexType]
        descTyDecl :: PDecl
        descTyDecl = PTy emptyDocstring [] defaultSyntax emptyFC [TotalFn] descName (descTy (PRef emptyFC unitTy))
        descClauses = PClauses emptyFC [TotalFn] descName [PClause emptyFC descName (PRef emptyFC descName) []
                   (switchDesc (foldr (flip (.) (\(_,_,_,term,_,_) -> descCns term) pairI) unitI cons)) []]
        natZ :: PTerm
        natZ = PRef emptyFC (sNS (sUN "Z") ["Nat", "Prelude"])
        natS :: PTerm -> PTerm
        natS t = PApp emptyFC (PRef emptyFC (sNS (sUN "S") ["Nat", "Prelude"])) [pexp t]
        unitI :: PTerm
        unitI = PRef emptyFC unitCon
        pairI :: PTerm -> PTerm -> PTerm
        pairI x y = PApp emptyFC (PRef emptyFC pairCon)
                        [pimp (sUN "A") Placeholder True, pimp (sUN "B") Placeholder True, pexp x, pexp y]
        eqRefl :: PTerm
        eqRefl = PApp emptyFC (PRef emptyFC eqCon) [pimp (sMN 0 "A") Placeholder True, pimp (sMN 0 "x") Placeholder True]
        dpairI :: PTerm -> PTerm -> PTerm
        dpairI x y = PApp emptyFC (PRef emptyFC existsCon)
                        [pimp (sUN "a") Placeholder True, pimp (sUN "P") Placeholder True, pexp x, pexp y]
        tagZ :: PTerm
        tagZ = PRef emptyFC (sNS (sUN "TZ") ["Generic", "Prelude"])
        tagS :: PTerm -> PTerm
        tagS t = PApp emptyFC (PRef emptyFC (sNS (sUN "TS") ["Generic", "Prelude"])) [pexp t]
        tagFromNum :: Integer -> PTerm
        tagFromNum n | n == 0 = tagZ
                     | n >  0 = tagS (tagFromNum (n - 1))
        dataCon :: PTerm -> PTerm
        dataCon inn = PApp emptyFC (PRef emptyFC (sNS (sUN "Con") ["Generic", "Prelude"])) [pexp inn]
        switchDesc :: PTerm -> PTerm
        switchDesc consmappings = PApp emptyFC (PRef emptyFC (sNS (sUN "switchDesc") ["Generic", "Prelude"])) [pexp consmappings]
        descRet :: PTerm -> PTerm
        descRet ixval = PApp emptyFC (PRef emptyFC (sNS (sUN "Ret") ["Generic", "Prelude"])) [pexp ixval]
        descRec :: PTerm -> PTerm -> PTerm
        descRec ixval rest = PApp emptyFC (PRef emptyFC (sNS (sUN "Rec") ["Generic", "Prelude"])) [pexp ixval, pexp rest]
        descArg :: PTerm -> PTerm -> PTerm
        descArg typ rest = PApp emptyFC (PRef emptyFC (sNS (sUN "Arg") ["Generic", "Prelude"])) [pexp typ, pexp rest]
        dataTy :: PTerm -> PTerm -> PTerm
        dataTy datadesc ixval = PApp emptyFC (PRef emptyFC (sNS (sUN "Data") ["Generic", "Prelude"])) [pexp datadesc, pexp ixval]
        descCns :: PTerm -> PTerm
        descCns (PPi _ nm ty rest) = descCnsArg nm ty (descCns rest)
        descCns _                  = descRet unitI
        descCnsArg :: Name -> PTerm -> PTerm -> PTerm
        descCnsArg nm ty@(PApp _ (PRef _ nm') _) rest
          | simpleName dn == simpleName nm' = descRec unitI rest
          | otherwise = descArg ty (PLam nm ty rest)
        descCnsArg nm ty@(PRef _ nm') rest
          | simpleName dn == simpleName nm' = descRec unitI rest
          | otherwise = descArg ty (PLam nm ty rest)
        descCnsArg nm ty rest = descArg ty (PLam nm ty rest)
        aliasName :: Name
        aliasName = uniqueName dn [dn]
        aliasTyDecl :: PDecl
        aliasTyDecl = PTy emptyDocstring [] defaultSyntax emptyFC [TotalFn] aliasName PType
        aliasClauses :: PDecl
        aliasClauses = PClauses emptyFC [TotalFn] aliasName [PClause emptyFC aliasName (PRef emptyFC aliasName) []
                         (dataTy (PRef emptyFC descName) unitI) []]
        aliasCnssTyDecl :: [PDecl]
        aliasCnssTyDecl = map (\(_,_,nm,ty,_,_) ->
                            PTy emptyDocstring [] defaultSyntax emptyFC [TotalFn] (aliasCnsNm nm) (aliasCnsTy ty)) cons
        aliasCnsTy :: PTerm -> PTerm
        aliasCnsTy ty@(PApp _ (PRef _ nm') args) 
          | simpleName dn == simpleName nm' = PApp emptyFC (PRef emptyFC aliasName) args
        aliasCnsTy ty@(PRef _ nm')
          | simpleName dn == simpleName nm' = PRef emptyFC aliasName
        aliasCnsTy ty@(PPi pl nm ty' rest) = PPi pl nm (aliasCnsTy ty') (aliasCnsTy rest)
        aliasCnsTy ty = ty
        aliasCnsNm :: Name -> Name
        aliasCnsNm nm = uniqueName nm [nm]
        aliasCnssClauses :: [PDecl]
        aliasCnssClauses = 
          map (\((_,_,nm,ty,_,_), i) ->
            let args = namePis . fst $ splitPi ty
            in PClauses emptyFC [TotalFn] (aliasCnsNm nm)
                 [PClause emptyFC (aliasCnsNm nm) (aliasCnsLhs nm args) [] (aliasCnsRhs nm i args) []])
                    (zip cons [0..])


        aliasCnsLhs :: Name -> [(Name, Plicity, PTerm)] -> PTerm
        aliasCnsLhs nm args =
           (PApp emptyFC (PRef emptyFC (aliasCnsNm nm))
              (map (\(arg, _, _) -> pexp (PRef emptyFC arg)) args))
        aliasCnsRhs :: Name -> Integer -> [(Name, Plicity, PTerm)] -> PTerm
        aliasCnsRhs nm i args = 
          dataCon
            (dpairI
              (PConstant . Str . show $ nm)
              (dpairI
              (tagFromNum i) (foldr (flip (.) (\(nm', pl, ty) -> PRef emptyFC nm') dpairI) eqRefl args)))

        namePis :: [(Name, Plicity, PTerm)] -> [(Name, Plicity, PTerm)]
        namePis = namePis' []
          where namePis' :: [(Name, Plicity, PTerm)] -> [(Name, Plicity, PTerm)] -> [(Name, Plicity, PTerm)]
            namePis' acc []                    = reverse acc
            namePis' acc ((nm, pl, ty):rest)   = namePis' ((uniqueName nm prevnm, pl, ty):acc) rest
               where prevnm :: [Name]
                     prevnm = map (\(nm, _, _) -> nm) acc
