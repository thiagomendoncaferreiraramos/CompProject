open import Data.String using (String; _≟_)
open import Relation.Nullary.Decidable using (Dec; yes; no; False; toWitnessFalse; ¬?)
open import Data.Nat.Base using (ℕ; zero; suc)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app; _≢_ )
open Eq.≡-Reasoning
open import Data.Empty using (⊥-elim)
open import Data.Product using (∃-syntax)

Id : Set
Id = String

infix  5  ƛ_⇒_
infixl 7  _·_
infix  9  `_

data Term : Set where
  `_                      :  Id → Term
  ƛ_⇒_                    :  Id → Term → Term
  _·_                     :  Term → Term → Term



infix 9 _[_:=_]

_[_:=_] : Term → Id → Term → Term

(` x) [ y := V ] with x ≟ y
... | yes _  = V
... | no _  = ` x

(ƛ x ⇒ N) [ y := V ] with x ≟ y
... | yes _         = ƛ x ⇒ N
... | no  _         = ƛ x ⇒ N [ y := V ]

(L · M) [ y := V ]  = L [ y := V ] · M [ y := V ]





data _#_ : Id → Term → Set where
  diff : {x y : Id} →
       x ≢ y →
       x # (` y)
       
  abs-eq : {x : Id} → {M : Term} → x # (ƛ x ⇒ M)

  abs-diff : {x y : Id} → {M : Term}
             → x # M
             → x # (ƛ y ⇒ M)

  app : {x : Id} → {M N : Term} →
        x # M
        → x # N
        → x # (M · N)


data _≡α_ : Term → Term → Set where
  Var-α : {x : Id} → (` x) ≡α (` x)
  App-α : {M M' N N' : Term}
          → M ≡α M'
          → N ≡α N'
       ----------------------------------
          → (M · N) ≡α (M' · N')

  Abs-α : {z x y : Id} →
          {M M' : Term} →
           z # M
         → z # M'
         → (M [ x := ` z ]) ≡α (M' [ y := ` z ])
         → (ƛ x ⇒ M) ≡α (ƛ y ⇒ M')

{-
#-exists : ∀(M : Term) → ∃[ x ] x # M
#-exists (` x) = {!!} Data.Product., {!!}
#-exists (ƛ x ⇒ M) = {!!}
#-exists (M · M₁) = {!!}

≡α-iden : ∀(M : Term) → M ≡α M
≡α-iden (` x) = Var-α
≡α-iden (ƛ x ⇒ M) = Abs-α {!!} {!!} {!!}
≡α-iden (M · M₁) = {!!}
-}


infix 4 _⋙_

data _⋙_ : Term → Term → Set where
  β : {x : Id} → {M N : Term}
  ------------------------------------------
      → ((ƛ x ⇒ M) · N) ⋙ (M [ x := N ])

  β-left : {M M' N : Term}
         → M ⋙ M'
         --------------------
         → M · N ⋙ M' · N

  β-right : {M N N' : Term}
         → N ⋙ N'
         --------------------
         → M · N ⋙ M · N'

 -- β-abs : {x : Id} → {M M` : Term}
 --       → M ⋙ M`
        ---------------------
  --      → ƛ x ⇒ M ⋙ M`

{- Reduction inside ƛ -}

infix 4 _⋙*_

data _⋙*_ : Term → Term → Set where
  ⋙1-step : {M N : Term}
            → M ⋙ N
            → M ⋙* N
            
  ⋙-refl : {M : Term}
           → M ⋙* M
           
  ⋙-trans : {M N P : Term}
            → M ⋙* N
            → N ⋙* P
            -----------------
            → M ⋙* P



subs : ∀(x y : Id) → ∀(N : Term) → x ≢ y → (` y) [ x := N ] ≡ ` y
subs x y N ne with y ≟ x  -- {!!}
...         | yes refl = ⊥-elim (ne refl)
...         | no _ = refl


fresh-subs : ∀(x : Id) → ∀(M N : Term) → x # M → M [ x := N ] ≡ M
fresh-subs x (` x₁) N (diff x₂) with x₁ ≟ x
...                   | yes refl =  ⊥-elim (x₂ refl)
...                   | no _ = refl
fresh-subs x (ƛ x₁ ⇒ M) N abs-eq with x₁ ≟ x
...                   | yes _ = refl
...                   | no  h = ⊥-elim (h refl)
fresh-subs x (ƛ x₁ ⇒ M) N (abs-diff P) with x₁ ≟ x
...                 | yes _ = refl
...                 | no _ rewrite cong (λ t → ƛ x₁ ⇒ t) (fresh-subs x M N P) = refl
fresh-subs x (M · M₁) N (app P P₁)
             rewrite cong (λ t → t · M₁ [ x := N ]) (fresh-subs x M N P) |
             cong (λ t → t) (fresh-subs x M₁ N P₁) = refl

fresh-subs⋙ : ∀(x : Id) → ∀(M N : Term) → x # M → M [ x := N ] ⋙* M
fresh-subs⋙ x M N f rewrite cong (λ t → t) (fresh-subs x M N f) = ⋙-refl



1reduction : Term → Term

1reduction ((ƛ x ⇒ M) · N) = (1reduction M) [ x := (1reduction N)]
1reduction (` x) = ` x
1reduction (M · N) = (1reduction M) · (1reduction N)
1reduction (ƛ x ⇒ M) = ƛ x ⇒ (1reduction M)

reduction : ℕ → Term → Term
reduction zero t = t
reduction (suc n) t = reduction n (1reduction t)
