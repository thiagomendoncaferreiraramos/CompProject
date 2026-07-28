open import TMmultipleTape
open import IMP
open import Data.Nat
open import Data.Vec renaming ([_] to ![_]!)
open import Data.List
open import Data.Product renaming (Σ to σ)
open import Data.Fin

toCase : {m n : ℕ} → Q m → Σ n →  Δ m n 1 → P
toCase q s δ with δ q ![ s ]!
...           | (q2 , (write s2) ∷ _) =  ( "q" := cnst (toℕ q2) ) ∷ ( "s" := cnst ) ∷ []
...            | _ = {!!}
