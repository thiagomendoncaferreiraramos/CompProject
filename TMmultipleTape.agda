open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; inject₁; fromℕ; toℕ)
open import Data.List using (List; []; _∷_; [_])
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; proj₁; proj₂; _,_)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Bool.Base as Bool
  using (Bool; false; true; not; _∧_; _∨_; if_then_else_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Vec using (Vec; []; _∷_)

--{-# BUILTIN NATURAL ℕ #-}



record Tape (Σ : Set) : Set where
  constructor tape
  field
    left : List Σ 
    head : Σ 
    right : List Σ 
open Tape public



data Move(Σ : Set) : Set where
  go_right : Move( Σ )
  go_left : Move( Σ )
  write : Σ → Move( Σ )


-- The type of Symbols
Σ : ℕ → Set
Σ n = Fin (suc (suc n))

-- The type of States
Q : ℕ → Set
Q = Σ




-- m number of states -2. n number of symbols -2 . o number of tapes
-- The type of Transition function
Δ : ℕ → ℕ → ℕ → Set
Δ m n o = Q m → Vec (Σ n) o → (Q m × Vec (Move (Σ n)) o)


record TM : Set where
  constructor tm
  field
    n-states : ℕ
    n-symbols : ℕ
    n-tapes : ℕ
    trans : Δ n-states n-symbols n-tapes
open TM public

record TM1tape : Set where
  constructor tm1
  field
    n-st : ℕ
    n-sym : ℕ
    trans1 : Δ n-st n-sym 1
open TM1tape public

TM1tape2TM : TM1tape → TM
TM1tape2TM (tm1 st sym δ) = tm st sym 1 δ 

-- The configuration
Config : TM → Set
Config (tm m n o _) = Q m × Vec (Tape (Σ n)) o


Heads : (n o : ℕ) → Vec (Tape (Σ n)) o → Vec (Σ n) o
Heads _ _ [] = []
Heads n (suc o) (t ∷ ts) = (head t) ∷ (Heads n o ts)


move-1-tape : {n : ℕ} → Move (Σ n) → Tape (Σ n) → Tape (Σ n)
move-1-tape go_right (tape l s []) = tape (s ∷ l) Fin.zero []
move-1-tape go_right (tape l1 s1 (s2 ∷ l2)) = tape (s1 ∷ l1) s2 l2
move-1-tape go_left (tape [] s l) = tape [] Fin.zero (s ∷ l)
move-1-tape go_left (tape (s1 ∷ l1) s2 l2) = tape l1 s1 (s2 ∷ l2)
move-1-tape (write w) (tape l1 s l2) = tape l1 w l2


move-n-tape : {o n : ℕ} → Vec (Move (Σ n)) o → Vec (Tape (Σ n)) o
              → Vec (Tape (Σ n)) o

move-n-tape [] [] = []
move-n-tape (m ∷ ms) (t ∷ ts) = (move-1-tape m t) ∷ (move-n-tape ms ts)

1-step : (tm : TM) → (Config tm) → (Config tm)
1-step (tm nst nsym nt δ) (st , tapes) =
       (proj₁ res , move-n-tape (proj₂ res) tapes)
  where res = δ st (Heads nsym nt tapes)

-- \rhd

data ▷(tm : TM) : Config tm → Config tm → Set where
  1-step-▷ : {c : Config tm} →
           ▷ tm c (1-step tm c)
           
data ▷*(tm : TM) : Config tm → Config tm → Set where
 
  0-step-▷ : {c : Config tm} →
             ▷* tm c c

  +s-step-▷ : {c1 c2 c3 : Config tm}
            → ▷ tm c1 c2
            → ▷* tm c2 c3
            ---------------
            → ▷* tm c1 c2
{-
 +s-stem-▷ : {c1 c2 c3 : Config tm}
            → 1-step-▷ tm c1 c2
            → ▷* tm c2 c3
            ---------------
            → ▷* tm c1 c3

-}
