open import TMmultipleTape
--open import Data.Fin
open import Data.Fin using (Fin; _↑ˡ_)
open import Data.List
--open import Data.Nat
open import Data.Nat using (ℕ; _+_; suc)
open import Data.Vec

shuffle : {n : ℕ} → List (Σ n) → List (Σ n) → List (Σ n)
shuffle [] [] = []
shuffle (a ∷ as) [] = a ∷ (Fin.suc Fin.zero) ∷ (shuffle as [])
shuffle [] (b ∷ bs) = (Fin.suc Fin.zero) ∷ b ∷ (shuffle [] bs)
shuffle (a ∷ as) (b ∷ bs) = a ∷ b ∷ (shuffle as bs)

multTape2one-aux : {n o : ℕ} → Vec (List (Σ n)) o → List (Σ n)
multTape2one-aux [] = []
multTape2one-aux (h ∷ t) = shuffle h (multTape2one-aux t)



head2TapeOne : {n : ℕ} → Fin n → Fin (n + suc n)
head2TapeOne {n} i = i ↑ˡ suc( n )


