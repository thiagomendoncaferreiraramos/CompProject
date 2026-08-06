open import TMtoIMP
open import IMP
open import Data.Bool renaming (_≟_ to _==B_)
open import Data.List renaming (reverse to rev)
open import Data.Product renaming (Σ to Σp)
open import TMmultipleTape
open import Relation.Binary.PropositionalEquality renaming ([_] to ![_]!)
open import Data.Nat renaming (_≟_ to _==N_)
open import Data.Fin renaming (_≟_ to _==F_)
open import Data.Vec using (Vec; []; _∷_; foldl; reverse) renaming ([_] to ?[_]? ; _++_ to _++v_ ; tail to tailV)


open import Data.Maybe renaming (map to mapM ; zip to zipM )

open import Data.String using (String; _≟_)
open import Relation.Nullary.Decidable using (Dec; yes; no; False; toWitnessFalse; ¬?)
open import Data.Nat.Base using (ℕ; zero; suc)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app; _≢_ )
open Eq.≡-Reasoning
open import Data.Empty using (⊥-elim)

BODY : Prog
BODY = heads:=Π-tapes ++
       REV-heads ++
      (vec2number "n-sym") ++
      ( mult-code "i" "number" "n-st") ++
      ( sum-code "i"  "i" "q") ++
        LOOKUP ++
        MOVES ++
        REV


{-
Zv : Val
Zv = K "Z" []

-}

Sv : Val → Val
Sv x = K "S" [ x ]

Fin2Val : {n : ℕ} → Fin n → Val
Fin2Val zero = Zv
Fin2Val (suc n) = Sv ( Fin2Val n )

ℕ2Val : ℕ → Val
ℕ2Val zero = Zv
ℕ2Val (suc n) = Sv (ℕ2Val n)

{-
VecTapes2Exp : {n o : ℕ} → Vec (Tape(Σ n)) o → Exp
VecTapes2Exp  [] = C "Nil" []
VecTapes2Exp  (t ∷ ts) = C "Cons" ((Tape2Exp t) ∷ [ VecTapes2Exp  ts ])
-}

semi2Val : {n : ℕ} → List (Σ n) → Val
semi2Val [] = K "Nil" []
semi2Val (s ∷ ss) = K "Cons" ((Fin2Val s) ∷ [ semi2Val ss ])

VecSym2Val : {n o : ℕ} → Vec (Σ n) o → Val
VecSym2Val [] = K "Nil" []
VecSym2Val (s ∷ ss) = K "Cons" ((Fin2Val s) ∷ [ VecSym2Val ss ])


Tape2Val : {n : ℕ} → Tape (Σ n) → Val
Tape2Val (tape l h r) = K "Triple" ((semi2Val l) ∷ (Fin2Val h) ∷ [ semi2Val r ])





VecTapes2Val : {n o : ℕ} → Vec (Tape(Σ n)) o → Val
VecTapes2Val  [] = K "Nil" []
VecTapes2Val  (t ∷ ts) = K "Cons" ((Tape2Val t) ∷ [ VecTapes2Val  ts ])

{-

sum-code : Id → Id → Id → Prog
sum-code res a1 a2 =  ( res := V a1 ) ∷
                      ( "aux" := V a2 ) ∷
                      [ while "aux" is
                              [ ("S" , ([ "x1" ] , ( res :=  S (V res) ) ∷
                                                   [ "aux" := V "x1" ])) ] ]

-}

lkup-upd2 : (res aux : Id) →
            (val : Val) →
            (m1 : List (Id × Val)) →
            (m1s : Mem) →
            (res ≢ aux) → (lkup (upd2 (aux , val) m1 m1s) res) ≡ lkup (m1 ∷ m1s) res
lkup-upd2 res aux val m1 [] neq with res ≟ aux
...                     | yes refl = ⊥-elim (neq refl)
...                     | no _ = refl
lkup-upd2 res aux val m1 (m ∷ ms) neq 
  with (elem aux (Data.List.map proj₁ m1))
lkup-upd2 res aux val m1 (m ∷ ms) neq | true with res ≟ aux
... | yes refl = ⊥-elim (neq refl)
... | no _ = refl
lkup-upd2 res aux val m1 (m ∷ ms) neq | false with (myLookup res m1)
... | just _  = refl
... | nothing = lkup-upd2 res aux val m ms neq


lkup-upd1 : (res aux : Id) →
            (val : Val) →
            (m1 : Mem) →
            (res ≢ aux) → (lkup (upd (aux , val) m1) res) ≡ lkup m1 res

lkup-upd1 res aux val [] neq = refl 
lkup-upd1 res aux val (m1 ∷ ms) neq = lkup-upd2 res aux val m1 ms neq





------------------------------------------------------

lkup-upd-same2 : (res : Id) →
            (val : Val) →
            (m1 : List (Id × Val)) →
            (m1s : Mem) →
            (lkup (upd2 (res , val) m1 m1s) res) ≡ val
lkup-upd-same2 res val m1 [] with res ≟ res
... | yes a = refl
... | no b = ⊥-elim (b refl)
  

lkup-upd-same2 res val m1 (m ∷ ms)
  with (elem res (Data.List.map proj₁ m1))  
...     | true with res ≟ res
...               |  yes q  = refl
...               | no w =  ⊥-elim (w refl)
lkup-upd-same2 res val m1 (m ∷ ms) | false
  with (myLookup res m1)
lkup-upd-same2 res val m1 (m ∷ ms) | false | nothing = lkup-upd-same2 res val m ms 
lkup-upd-same2 res val m1 (m ∷ ms) | false | just s = {!!}



-------------------------------------------------------

lkup-upd-same : (res : Id) →
            (val : Val) →
            (m1 : Mem) →
            (lkup (upd (res , val) m1) res) ≡ val
lkup-upd-same res val m1 = {!!}

sum-code-Body : Id → Prog
sum-code-Body res = ( res :=  S (V res) ) ∷
                     [ "aux" := V "x1" ]


sum-code-inv : (r a : ℕ) →
               (res : Id) →
               (m1 m2 : Mem) →
               res ≢ "aux" → 
               (ℕ2Val r) ≡ (lkup m1 res) →
               (ℕ2Val (suc a)) ≡ (lkup m1 "aux") →
               (ℕ2Val a) ≡ (lkup m1 "x1") →
               (m1 , (sum-code-Body res)) ▸* (m2 , []) →
               (ℕ2Val (suc r)) ≡ (lkup m2 res)
               
sum-code-inv r a res m1 m2 neq r-res sa-aux a-x1
             (trans-▸ st1 st2 st3 (asg-I)
               (trans-▸ st4 st5 st6 (asg-I)
               (refl-▸ B))) rewrite Eq.trans (refl) (lkup-upd1 res "aux" (eval (upd (res , eval m1 (S (V res))) m1) (V "x1")) (upd (res , eval m1 (S (V res))) m1) neq) | Eq.cong Sv r-res = {!!}


{-



lkup
(upd ("aux" , eval (upd (res , eval m1 (S (V res))) m1) (V "x1"))
 m1)
res
≡ lkup m1 res

-}



-- The code inputs the codified tapes and returns the reversed list of heads.
heads:=Π-tapes-revHeads : (m1 m2 : Mem) →
                        (n o : ℕ) →
                        (tapes : Vec (Tape (Σ n)) o) → 
                         VecTapes2Val tapes ≡ lkup m1 "tapes" →
                        (m1 , heads:=Π-tapes) ▸* (m2 , []) →
                        VecSym2Val (reverse (Heads n o tapes)) ≡ lkup m2 "heads"
heads:=Π-tapes-revHeads = {!!}

rev-heads : (m1 m2 : Mem) →
            (n o : ℕ) →
            (rev-head : Vec (Σ n) o) →
            VecSym2Val rev-head ≡ lkup m1 "heads" →
            (m1 , heads:=Π-tapes) ▸* (m2 , []) →
            (VecSym2Val (reverse rev-head) ≡ lkup m1 "heads")

rev-heads = {!!}

--Body performs one step of the Turing Machine
BODY-is-1stepST : (m1  m2 : Mem) →
                (tm : TM) →
                (c : Config tm) →
                (Fin2Val (proj₁ c)) ≡ (lkup m1 "q") →
                 (VecTapes2Val (proj₂ c)) ≡ (lkup m1 "tapes") →
                 (eval m1 (δ2Table (TM.trans tm))) ≡ (lkup m1 "table") → 
                (m1 , BODY) ▸* (m2 , []) →
                (Fin2Val (proj₁ (1-step tm c))) ≡ (lkup m2 "q")


--TM2IMP

{- TODO : After proving the last theorem, finish to specify it.
  TM2IMP-is-stepST* : (m1 m2 : Mem) →
                  ()
                  (c1 c2 : Config tm) →
                  (m1 , TM2IMP) ▸* (m2 , []) →
                  
-}

BODY-is-1stepST = {!!}

