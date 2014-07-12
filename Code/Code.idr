module Code

data Desc : (ix : Type) -> Type where
  Ret  : ix -> Desc ix
  Arg  : (a : Type) -> (a -> Desc ix) -> Desc ix
  Rec  : ix -> Desc ix -> Desc ix

VecDesc : (a : Type) -> Desc Nat
VecDesc a =
  Arg Bool
  (\isNil => if isNil
              then Ret Z
              else Arg Nat (\n=>
                 Arg a (\x=> Rec n (Ret (S n)))))

CLabel : Type
CLabel = String

CEnum : Type
CEnum = List CLabel

VecCtors : CEnum
VecCtors = [ "Nil" , "Cons" ]

data Tag : CLabel -> CEnum -> Type where
  TZ : Tag l (l :: e)
  TS : Tag l e -> Tag l (l' :: e)

SPi : (e : CEnum) -> (prop : (l : CLabel) -> (t : Tag l e) -> Type) ->   Type
SPi []        prop = ()
SPi (l :: e)  prop =
  (prop l TZ, SPi e (\l',t => prop l' (TS t)))

switch : (e : CEnum)
   -> (prop : (l : CLabel) -> (t : Tag l e) -> Type)
   -> SPi e prop
  -> ((l' : CLabel) -> (t' : Tag l' e) -> prop l' t')
switch (l' :: e) prop ((propz, props)) l' TZ      = propz
switch (l  :: e) prop ((propz, props)) l' (TS t') =
  switch e (\ l, t => prop l (TS t)) props l' t'

VecDesc' : (a : Type) -> Desc Nat
VecDesc' a =
  Arg CLabel (\l=>
    Arg (Tag l VecCtors)
      ((switch VecCtors (\l=> \t=> Desc Nat)
        ( Ret Z
        , (Arg Nat (\n=>
           Arg a (\x=> Rec n (Ret (S n))))
        , () ) )) l))

Synthesise : Desc ix -> (ix -> Type) -> (ix -> Type)
Synthesise (Ret j)      x i = (j = i)
Synthesise (Rec j d)    x i =
  (rec : x j ** Synthesise d x i)
Synthesise (Arg a d)    x i =
  (arg : a ** Synthesise (d arg) x i)

data Data : {ix : Type} -> Desc ix -> ix -> Type where
  Con : {d : Desc ix} -> {i : ix}
      -> Synthesise d (Data d) i -> Data d i

Vec : (a : Type) -> Nat -> Type
Vec a n = Data (VecDesc' a) n 

exampleVec : Vec Nat 3
exampleVec = Con ("Cons" ** (TS TZ ** (2 ** (1 **
         (Con ("Cons" ** (TS TZ ** (1 ** (2 **
           (Con ("Cons" ** (TS TZ ** (0 ** (3 **
            (Con ("Nil" ** (TZ ** refl)) ** refl)
                   )))) ** refl)
                )))) ** refl)
              ))))

Nil : {a : Type} -> Vec a Z
Nil = Con ("Nil" ** (TZ ** refl)) 
 
Cons : {a : Type} -> {n : Nat}
    -> a -> Vec a n -> Vec a (S n)
Cons {n} x xs = Con ("Cons" ** (TS TZ ** (n ** 
              (x ** (xs ** refl))))) 

exampleVec' : Vec Nat 3
exampleVec' = Cons 1 (Cons 2 (Cons 3 Nil))

