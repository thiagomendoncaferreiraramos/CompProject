open import TMmultipleTape
open import IMP
open import Data.List
open import Data.List.Base
open import Data.Nat using (ℕ; zero; suc; ⌊_/2⌋; _+_; _*_; _/_; _%_; _<_; _^_)
open import Data.Product renaming (Σ to Σp)
open import Data.Vec renaming ([_] to ![_]! ; _++_ to _++v_ ; tail to tailV)
open import Data.Fin using (Fin; fromℕ<; toℕ; zero; suc) renaming (_+_ to _+F_)
--open import Data.Maybe
open import Relation.Binary.PropositionalEquality renaming ([_] to ?[_]?)
open import Data.Nat.DivMod


Zv : Val
Zv = K "Z" []

Z : Exp
Z = val2exp Zv

S : Exp → Exp
S x = C "S" [ x ]

{-
MOVE-LEFT : Prog
MOVE-LEFT =  ( "right" := C "Cons"  ((V "s" ) ∷ (V "right") ∷ [])) ∷
              [ case "left" of
                (("Nil" ,( [] , [ "s" := Z ] ) ) ∷
                [ ( "Cons" , ( "sl" ∷ [ "lefts" ] ,
                           "s" := V "sl" ∷ [ "left" := V "lefts" ])) ] ) ]
-}
{-
MOVE-RIGHT : Prog
MOVE-RIGHT = ( "left" := C "Cons"  ((V "s" ) ∷ (V "left") ∷ [])) ∷
              [ case "left" of
                (("Nil" ,( [] , [ "s" := Z ] ) ) ∷
                [ ( "Cons" , ( "sr" ∷ [ "rights" ] ,
                           "s" := V "sr" ∷ [ "right" := V "rights" ])) ] ) ]
-}


Fin2Exp : {n : ℕ} → Fin n → Exp
Fin2Exp zero = Z
Fin2Exp (suc n) = C "S" [ (Fin2Exp n) ]

{-
pair : Exp → Exp → Exp
pair a b = C "Pair" (a ∷ [ b ])
-}
Move2Exp : {n : ℕ} → Move (Q n) → Exp
Move2Exp go_right = C "R" []
Move2Exp go_left = C "L" []
Move2Exp (write w) = C "W" [ (Fin2Exp w) ]


{-
Trans2Table : {m n : ℕ} → Q m → Σ n →  Δ m n 1 → Exp
Trans2Table q s σ with σ q (s ∷ [])
...                | (q2 ,  m ∷ []) = pair (pair (Fin2Exp q) (Fin2Exp s)) (pair (Fin2Exp q2) (Move2Exp m))

-}

{-
ℕ2Fin : {n : ℕ} → ℕ → Fin (suc n)
ℕ2Fin zero = Fin.zero
ℕ2Fin {zero} _ = Fin.zero
ℕ2Fin {suc n} (suc i) = Fin.suc (ℕ2Fin {n} i)
-}
{-
δ2T-1 : {m n : ℕ} →  Δ m n 1 → Q m → ℕ → List Exp
δ2T-1 δ q zero = [ Trans2Table q (ℕ2Fin zero) δ ]
δ2T-1 δ q (suc n) = (Trans2Table q (ℕ2Fin (suc n)) δ) ∷
                        (δ2T-1 δ q n)
-}
{-
δ2T-2 : {m n : ℕ} → Δ m n 1 → ℕ → List Exp
δ2T-2 {m} {n}  δ zero = δ2T-1 δ (ℕ2Fin zero) (suc (suc n))
δ2T-2 {m} {n} δ (suc i) = (δ2T-1 δ (ℕ2Fin (suc i)) (suc (suc n))) ++ (δ2T-2 δ i)
-}
listExp2Exp : List Exp → Exp
listExp2Exp [] = C "Nil" []
listExp2Exp (h ∷ hs) = C "Cons" ((h) ∷ (listExp2Exp hs) ∷ [])

{-
δ2T : {m n : ℕ} → Δ m n 1 → Exp
δ2T {m} {n} δ = listExp2Exp (δ2T-2 δ (suc (suc m)))
-}
{-
b:=s==sn : Prog
b:=s==sn = [ while "s" is
                   ( ( "Z" , ([] ,
                      [ case "sn" of
                             (( "Z" , ([] , [ "b" := C "True" [] ])) ∷
                             [ ("S", ([ "m" ] , [ "b" := C "False" [] ])) ] ) ])) ∷ 
                    [ ("S" ,([ "n" ] ,
                           [ case "sn" of
                                   ( ("Z" , ([] , [ "b" := C "False" [] ])) ∷
                                   [ ("S" , ([ "m" ] ,
                                          (("s" := V "n") ∷ [ ("sn" := V "m") ]))) ] ) ])) ] ) ]
-}
{-
b:=q==qn : Prog
b:=q==qn = [ while "q" is
                   ( ( "Z" , ([] ,
                      [ case "qn" of
                             (( "Z" , ([] , [ "b" := C "True" [] ])) ∷
                             [ ("S", ([ "m" ] , [ "b" := C "False" [] ])) ] ) ])) ∷ 
                    [ ("S" ,([ "n" ] ,
                           [ case "qn" of
                                   ( ("Z" , ([] , [ "b" := C "False" [] ])) ∷
                                   [ ("S" , ([ "m" ] ,
                                          (("q" := V "n") ∷ [ ("qn" := V "m") ]))) ] ) ])) ] ) ]
  -}
{-
b:=qs==p1 : Prog
b:=qs==p1 = [ case "p1p2" of
                    [ ("Pair" , (("p1") ∷ [ "p2" ] ,
                              [ case "p1" of
                                     [ ( "Pair" , ( "qn" ∷ [ "sn" ] ,
                                                b:=q==qn ++
                                                [ case "b" of
                                                       (( "False" , ( [] , [ "skip" := NullE ])) ∷
                                                     [ ( "True" , ( [] , b:=s==sn)) ]) ])) ] ] )) ] ]
-}
{-
qa:=q2 : Prog
qa:=q2 = [ case "p1p2" of
                [ ("Pair" , ("p1" ∷ [ "p2" ] ,
                          [ case "p2" of
                               [ ("Pair" , ( "ai" ∷ [ "qi" ] ,
                                         (("q" := V "qi") ∷
                                         [ "a" := V "ai" ]) )) ] ] )) ] ]

-}
{-
LOOKUP-1T : TM1tape → Prog
LOOKUP-1T (tm1 nq ns δ) = ("l" := δ2T δ) ∷
                       [ while "l" is
                               [ ("Cons" , ( "p1p2" ∷ [ "resto" ] ,
                                         (b:=qs==p1) ++
                                         (case "b" of
                                               (("False" , ( [] , [ "skip" := NullE ] )) ∷
                                               [ ("True" , ( [] , qa:=q2 )) ])) ∷
                                         [ "l" := V "resto" ])) ] ]
-}

{-
TM2IMP1tape : TM1tape → Prog
TM2IMP1tape t = ( "q" := S Z ) ∷
         ( while "q" is 
                  [ ("S" , ([ "x" ] ,
                         ( LOOKUP-1T t) ++
                         ( case "a" of
                                 ( ("L" , ([] , MOVE-LEFT)) ∷
                                  ("R" , ([] , MOVE-RIGHT)) ∷
                                  ("W" , ([ "ns" ] , [ "s" := V "ns" ])) ∷ []) ) ∷ [])) ] ) ∷ []
                  

-}

myTail : Prog → Prog
myTail [] = []
myTail (x ∷ xs) = xs


----------------------------------------------------

sum-code : Id → Id → Id → Prog
sum-code res a1 a2 =  ( res := V a1 ) ∷
                      ( "aux" := V a2 ) ∷
                      [ while "aux" is
                              [ ("S" , ([ "x1" ] , ( res :=  S (V res) ) ∷
                                                   [ "aux" := V "x1" ])) ] ]
mult-code : Id → Id → Id → Prog
mult-code res a1 a2 =  ( res :=  Z ) ∷
                       ( "aux" := V a2) ∷
                       [ while "aux" is
                              [ ("S" , ([ "x1" ] , ( sum-code res res a1 ) ++
                                                   [ "aux" := V "x1" ])) ] ]

vec2number2 : Id → Prog
vec2number2 k = ( "number" := Z ) ∷
             [ while "vec" is
                     [ ("Cons" , ( "h" ∷ [ "t" ]  ,
                               (sum-code "number" "number" "h") ++
                               ( case "t" of
                                      ( ( "Nil" , ([] , [ "skip" := NullE ]) ) ∷
                                       [ ("Cons" , ( "nh" ∷ [ "nt" ] ,  mult-code "number" "number" k )) ] ) ) ∷
                               [ "vec" := V "t" ] ) ) ] ]


heads2number : Id → Prog
heads2number k = ( "number" := Z ) ∷
                [ while "heads" is
                        [("Cons" , ( ("x" ∷ [ "xs" ]) ,
                                     (("heads" := V "xs") ∷
                                       (mult-code "res" "number" k) ++
                                       (sum-code "number" "x" "res")
                                     ) ))] ]


Heads2ℕ : {o : ℕ} → (n : ℕ) → Vec (Σ n) o → ℕ
Heads2ℕ _ [] = zero
Heads2ℕ n (x ∷ xs) = (toℕ x) +  suc( suc n) * (Heads2ℕ n xs)

{-
Heads2ℕn : {o : ℕ} → (n : ℕ) → Vec (ℕ) o → ℕ
Heads2ℕn  n xs = go xs 0
  where
    go : Vec (ℕ) o → ℕ → ℕ
    go [] acc = acc
    go (x ∷ xs) acc =
      go xs (x + suc (suc n) * acc)
-}

ℕ2Heads : ∀ {o n} → ℕ → Vec (Σ n) o
ℕ2Heads {zero}  {_} _ = []
ℕ2Heads {suc o} {n} m =
  let b   = suc (suc n)
      q   = m div b
      r   = m mod b
  in r ∷ ℕ2Heads {o} {n} q


Stateℕ2ℕ : {n : ℕ} → Q n → ℕ → ℕ
Stateℕ2ℕ {n} q i = (toℕ q) + suc( suc n) * i

ℕ2Stateℕ : {n : ℕ} → ℕ → Q n × ℕ
ℕ2Stateℕ {n} x = (q , i)
  where
    k : ℕ
    k = suc (suc n)

    i : ℕ
    i = x / k

    q : Q n
    q = x mod k

   


Lmove2Exp : {n o : ℕ} → Vec (Move (Σ n)) o → Exp
Lmove2Exp [] = C "Nil" []
Lmove2Exp (m ∷ ms) = C "Cons" ((Move2Exp m) ∷ [ (Lmove2Exp ms) ])

ℕ2Exp : ℕ → Exp
ℕ2Exp zero = Z
ℕ2Exp (suc n) = S (ℕ2Exp n)

δ2Table-aux : {m n o : ℕ} → Δ m n o → ℕ → Exp
δ2Table-aux {m} {n} {o} δ i with δ (proj₁ (ℕ2Stateℕ i)) (ℕ2Heads (proj₂ (ℕ2Stateℕ {n} i)))
...                | (q2 ,  lmove) = C "Triple" (( ℕ2Exp i ) ∷ (Fin2Exp q2) ∷ [ (Lmove2Exp lmove) ])

δ2Table1 : {m n o : ℕ} → Δ m n o → ℕ → List Exp
δ2Table1 δ zero = [ δ2Table-aux δ zero ]
δ2Table1 δ (suc n) = (δ2Table-aux δ (suc n)) ∷ (δ2Table1 δ n)

-- In the table, we represents the arguments Q n and Vec (Σ n) as a ℕ. 
δ2Table : {m n o : ℕ} → Δ m n o → Exp
δ2Table {m} {n} {o} δ = listExp2Exp
                (δ2Table1 δ (suc (suc m) * suc( suc n) ^ o))


semi2Exp : {n : ℕ} → List (Σ n) → Exp
semi2Exp [] = C "Nil" []
semi2Exp (s ∷ ss) = C "Cons" ((Fin2Exp s) ∷ [ semi2Exp ss ])

Tape2Exp : {n : ℕ} → Tape (Σ n) → Exp
Tape2Exp (tape l h r) = C "Triple" ((semi2Exp l) ∷ (Fin2Exp h) ∷ [ semi2Exp r ])

-- Mapping tapes to single expressions.

VecTapes2Exp : {n o : ℕ} → Vec (Tape(Σ n)) o → Exp
VecTapes2Exp  [] = C "Nil" []
VecTapes2Exp  (t ∷ ts) = C "Cons" ((Tape2Exp t) ∷ [ VecTapes2Exp  ts ])

--VecTape2Exp : {n : ℕ} →

heads:=Π-tapes : Prog
heads:=Π-tapes = ( "heads" := C "Nil" [] ) ∷
                  ( "t" := V "tapes" ) ∷ 
                  [ while "t" is
                    [ ( "Cons" , ( ("ht") ∷ [ "tt" ] ,
                                          ( case "ht" of
                                                 [ ("Triple" , ("l" ∷ "h" ∷ [ "r" ] ,
                                                             [ "heads" := C "Cons" ((V "h") ∷ [ V "heads" ])])) ] ) ∷ 
                                          [ "t" := V "tt" ])) ] ]



b:=index==i : Prog
b:=index==i = ("n-index" := V "index") ∷
              ("n-i" := V "i") ∷
              ("halt" := C "False" []) ∷
              [ while "halt" is
                      ([( "False" , ([] ,
                                  [ case "n-index" of
                                         ( ("Z" , ([] ,
                                                [ case "n-i" of
                                                      ( ("Z" , ([] ,
                                                             ( ("halt" := C "True" [] ) ∷
                                                               [ "b" := C "True" [] ]) )) ∷
                                                       [ ("S" , ([ "z" ] ,
                                                              (("halt" := C "True" []) ∷
                                                              [ "b" := C "False" [] ]) )) ] ) ] ))  ∷
                                            [ ("S" , ([ "z" ] ,
                                                   [ case "n-i" of
                                                    ( ("Z" , ([] ,
                                                             ( ("halt" := C "True" [] ) ∷
                                                               [ "b" := C "False" [] ]) )) ∷
                                                       [ ("S" , ([ "y" ] ,
                                                              (("n-i" := V "y") ∷
                                                              [ "n-index" := V "z" ]) )) ] ) ] )) ] ) ]))] ) ]

LOOKUP : Prog
LOOKUP = ( "t" := V "table" ) ∷
         [ while "t" is
           [ ( "Cons" , ("y" ∷ [ "ys" ])  ,
               [ case "y" of
                      [ ("Triple" , ("i" ∷ "qn" ∷ [ "lmoves" ] ,
                                  (b:=index==i) ++
                                  [ case "b" of
                                         (("True", ([] ,
                                                   (("t" := C "Nil" [] ) ∷
                                                   ("q" := V "qn") ∷
                                                   [ "moves" := V "lmoves" ]) )) ∷
                                          [ ("False" , ([] ,
                                                   [ "t" := V "ys" ])) ]) ] )) ] ] ) ] ]


LEFT : Id → Id → Id → Id → Prog
LEFT t l h r = [ case l of
                     (("Nil" , ([] ,
                             [ t := C "Triple" ((V l) ∷ Z ∷ [ C "Cons" ((V h) ∷ [ (V r) ])  ]) ])) ∷ 
                     [ ("Cons" , ( ("y" ∷ [ "ys" ]) ,
                             [ t := C "Triple" ((V "ys") ∷ (V "y") ∷ [ C "Cons" ((V h) ∷ [ (V r) ])  ])])) ]) ]

RIGHT : Id → Id → Id → Id → Prog
RIGHT t l h r = [ case l of
                     (("Nil" , ([] ,
                             [ t := C "Triple" (( C "Cons" ((V h) ∷ [ (V l) ])  ) ∷ Z ∷ [ (V r) ]) ])) ∷ 
                     [ ("Cons" , ( ("y" ∷ [ "ys" ]) ,
                              [ t := C "Triple" (( C "Cons" ((V h) ∷ [ (V l) ])  ) ∷ (V "y") ∷ [ (V "ys") ]) ])) ]) ]

MOVE1TAPE : Id → Id → Prog
MOVE1TAPE t m = [ case t of
                       [ ("Triple" , (("left" ∷ "head" ∷ [ "right" ]) ,
                                   ([ case m of
                                           (("L" , ([] , (LEFT t "left" "head" "right") )) ∷
                                           ("R", ([] , (RIGHT t "left" "head" "right"))) ∷
                                           [ ("W" , ([ "s" ] ,
                                                  [ t := C "Triple" ((V "left") ∷ (V "s") ∷ [ (V "right" ) ]) ])) ]) ]) )) ] ]

MOVES : Prog
MOVES = ( "ans" := C "Nil" []) ∷
        ( "n-moves" := V "moves" ) ∷
        ( "n-tapes" := V "tapes" ) ∷ 
        [ while "n-tapes" is
                [ ("Cons" , ( ( "t" ∷ [ "ts" ] ) ,
                          ( 
                          [ case "n-moves" of
                                 ([ ("Cons" , (( "m" ∷ [ "ms"  ]) ,
                                           ( (MOVE1TAPE "t" "m") ++
                                             ( "ans" := C "Cons" ((V "t") ∷ [ V "res" ]) ) ∷
                                             ("n tapes" := V "ts") ∷ 
                                             [ ("n-moves" := V "ms") ] ))) ]) ] ))) ] ]

REV : Prog
REV = ("tapes" := C "Nil" []) ∷
      [ while "ans" is
              [ ("Cons" , ( ("x" ∷ [ "xs" ]),
                        ( ("tapes" := C "Cons" ((V "x") ∷ [ V "tapes" ] )) ∷ 
                        [ "ans" := V "xs" ]))) ] ]

REV-heads : Prog
REV-heads = ("headss" := C "Nil" []) ∷
      ( while "heads" is
              [ ("Cons" , ( ("x" ∷ [ "xs" ]),
                        ( ("headss" := C "Cons" ((V "x") ∷ [ V "headss" ] )) ∷ 
                        [ "heads" := V "xs" ]))) ] ) ∷
      [ "heads" := V "headss" ]

TM2IMP : {o : ℕ} → (m n : ℕ) → Vec (Tape (Σ n)) o → Δ m n o →  Prog
TM2IMP n-st n-sym tapes δ =
         ( "q" := S Z ) ∷
         ( "tapes" := VecTapes2Exp tapes ) ∷
         ( "table" := δ2Table δ ) ∷
         ( "n-sym" := S (S (ℕ2Exp n-sym)) ) ∷
         ( "n-st" := S (S (ℕ2Exp n-st)) ) ∷
         [ while "q" is
                 [( "S" , ([ "x" ] ,
                        heads:=Π-tapes ++
                        REV-heads ++
                        (heads2number "n-sym") ++
                        ( mult-code "i" "number" "n-st") ++
                        ( sum-code "i"  "i" "q") ++
                        LOOKUP ++
                        MOVES ++
                        REV
                        ))] ]

{-

--δ2Table1
δ2Table1 : {m n o : ℕ} →  Δ m n o → Q m → ℕ → List Exp
δ2Table1 δ q zero = [ δ2Table-aux δ q (ℕ2Heads zero) ]
δ2Table1 δ q (suc n) = (δ2Table-aux δ q (ℕ2Heads (suc n)) ) ∷
                        (δ2Table1 δ q n)


δ2Table2 : {m n o : ℕ} → Δ m n o → ℕ → List Exp
δ2Table2 {m} {n} {o}  δ zero = δ2Table1 δ (ℕ2Fin zero) (suc (suc n))
δ2Table2 {m} {n} {o} δ (suc i) = (δ2Table1 δ (ℕ2Fin (suc i)) (suc (suc n))) ++ (δ2Table2 δ i)

δ2Table : {m n o : ℕ} → Δ m n o → Exp
δ2Table {m} {n} δ = listExp2Exp (δ2Table2 δ (suc (suc m)))


LOOKUP-Mult : TM → Prog
LOOKUP-Mult (tm nq ns no δ) = ("l" := δ2Table δ) ∷
                       [ while "l" is
                               [ ("Cons" , ( "p1p2" ∷ [ "resto" ] ,
                                         (b:=qs==p1) ++
                                         (case "b" of
                                               (("False" , ( [] , [ "skip" := NullE ] )) ∷
                                               [ ("True" , ( [] , qa:=q2 )) ])) ∷
                                         [ "l" := V "resto" ])) ] ]

-}
