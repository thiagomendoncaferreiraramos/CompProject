open import Data.String renaming (map to mapS ; _++_ to _app_)
open import Data.List
open import Data.Product renaming (map to mapP ; zip to zipP)
open import Data.Maybe renaming (map to mapM ; zip to zipM)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality renaming ([_] to ![_]!)

open import Data.Unit renaming (_≟_ to _==U_)
open import Data.Empty
open import Data.Bool renaming (_≟_ to _==B_)

Id : Set
Id = String

data Val : Set where
  K : Id → List Val → Val
  NullV : Val

data Exp : Set where
  V : Id → Exp
  C : Id → List Exp → Exp
  NullE : Exp

Prog : Set
data Instr : Set


Prog = List Instr
Branch : Set
Branch = (Id × (List Id × Prog))


data Instr  where
  _:=_ : Id → Exp → Instr
  case_of_ : Id → List Branch → Instr
  while_is_ : Id → List Branch → Instr
  pop : Instr
  local : List Id → Prog → Instr


exp2listexp : Exp → List Exp
exp2listexp (C id vs) = vs
exp2listexp _ = []

{- problem with termination
val2exp : Val → Exp
val2exp NullV = NullE -- In the original file, there is not this case
val2exp (K id vs) = C id (map val2exp vs)
-}

myVal2exp : Val → Exp
myVal2exp NullV = NullE -- In the original file, there is not this case
myVal2exp (K id []) = C id []
myVal2exp (K id (v ∷ vs)) = C id ((myVal2exp v) ∷ (exp2listexp (myVal2exp (K id vs))))

val2exp : Val → Exp
val2exp = myVal2exp

Mem : Set
Mem = List (List (Id × Val))


push : List (Id × Val) → Mem → Mem
push f m = f ∷ m 


myLookup : Id → List (Id × Val) → Maybe Val
myLookup x [] = nothing
myLookup x ((id , v) ∷ t) with x ≟ id
...                        | yes _ = just v
...                        | no _ = myLookup x t

myLookup2 : Id → List Branch → Maybe (List Id × Prog)
myLookup2 x [] = nothing
myLookup2 x ((id , v) ∷ t) with x ≟ id
...                        | yes _ = just v
...                        | no _ = myLookup2 x t

lkup : Mem → Id → Val
lkup [] x = NullV -- In the original file there is an error message.
lkup (h ∷ t) x  with (myLookup x h)
...               | just v = v
...               | nothing = lkup t x


elem : Id → List Id → Bool
elem x [] = false
elem x (id ∷ ids) with x ≟ id
...               | yes _ = true
...               | no _ = elem x ids

---------------------------------------
contradict : true ≡ false → ⊥
contradict ()

elem-myLookup : (res : Id) →
                (m1 : List (Id × Val)) →
                (elem res (map proj₁ m1)) ≡ false →
                (myLookup res m1) ≡ nothing
elem-myLookup res [] eq = refl
elem-myLookup res (m1 ∷ m1s) eq with  (elem res (map proj₁ ( m1 ∷ m1s ))) ==B false
elem-myLookup res (m1 ∷ m1s) eq    | yes h with res ≟ (proj₁ m1)
...                      | yes q = ⊥-elim( contradict eq)
...                      | no k = elem-myLookup res m1s eq
elem-myLookup res (m1 ∷ m1s) eq    | no f = ⊥-elim (f eq) 
---------------------------------------

{- Problems with termination
upd : (Id × Val) → Mem → Mem
upd p [] = []
-- Is it possible to eliminate this line?
upd p (f ∷ []) = Data.List.[ (p ∷ f) ]
upd p (f ∷ g ∷ fs) with elem (proj₁ p) (map proj₁ f)
...              | true = (p ∷ f) ∷ g ∷ fs
...              | false = f ∷ (upd p (g ∷ fs))
-}

upd2 : (Id × Val) → List (Id × Val) → Mem → Mem



upd2 p f [] = [ p ∷ f ]
upd2 p f (g ∷ fs) with elem (proj₁ p) (map proj₁ f)
... | true  = (p ∷ f) ∷ g ∷ fs
... | false = f ∷ upd2 p g fs

upd : (Id × Val) → Mem → Mem
upd p [] = []
upd p (f ∷ fs) = upd2 p f fs

val2listval : Val → List Val
val2listval (K id vs) = vs
val2listval _ = []

{- problem with termination
eval : Mem → Exp → Val
eval m (V x) = lkup m x
eval m (C id exps) = K id (map (eval m) exps)
-}

myEval : Mem → Exp → Val
myEval m (V x) = lkup m x
myEval m (C id []) = K id []
myEval m (C id (e ∷ exps)) = K id ((myEval m e) ∷ (val2listval (myEval m (C id exps))))
myEval m NullE = NullV

eval : Mem → Exp → Val
eval = myEval


data _▸_ : (Mem × Prog) → (Mem × Prog) → Set where
  asg-I : {m : Mem} → {id : Id} → {exp : Exp} → {p : Prog} → 
    (m , (id := exp) ∷ p) ▸ (upd (id , eval m exp) m , p)
  pop-I : {m : List (Id × Val)} → {ms : Mem} → {p : Prog} →
    (m ∷ ms , pop ∷ p) ▸ (ms , p)
  local-I : {m : Mem} → {xs : List Id} → {p1 p2 : Prog} →
    (m , (local xs p1) ∷ p2) ▸ (push (map (λ {x → (x , NullV)}) xs) m , p1 ++ (pop ∷ p2))
  case-I : {m : Mem} → {x c : Id} → {vs : List Val} → {xs : List Id} → {bs : List Branch} → {p1 p2 : Prog} → 
          K c vs ≡ lkup m x → just (xs , p2) ≡  myLookup2 c bs → 
     (m , (case x of bs) ∷ p1 ) ▸ (push (zip xs vs) m , p2 ++ (pop ∷ p1))
  while0-I : {m : Mem} → {x c : Id} → {vs : List Val} → {xs : List Id} → {bs : List Branch} → {p1 p2 : Prog} → 
          K c vs ≡ lkup m x → just (xs , p2) ≡  myLookup2 c bs → 
     (m , (while x is bs) ∷ p1 ) ▸ (push (zip xs vs) m , p2 ++ (pop ∷ ((while x is bs) ∷ p1)))
  while1-I : {m : Mem} → {x c : Id} → {vs : List Val} → {bs : List Branch} → {p1 p2 : Prog} → 
          K c vs ≡ lkup m x → nothing ≡  myLookup2 c bs → 
     (m , (while x is bs) ∷ p1 ) ▸ (m , p1)


data _▸*_ : (Mem × Prog) → (Mem × Prog) → Set where
  refl-▸ : (st : Mem × Prog) → st ▸* st
  --1step-▸ : (st1 st2 : Mem × Prog) → st1 ▸ st2 →
  --          st1 ▸* st2
  trans-▸ : (st1 st2 st3 : Mem × Prog) →
            st1 ▸ st2 → st2 ▸* st3 → st1 ▸* st3

