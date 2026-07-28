module Krivine where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product using (_×_; _,_)

-- λ-calculus terms using Bruijn indices.
data TermB : Set where
  var : ℕ -> TermB
  lam : TermB -> TermB
  app : TermB -> TermB -> TermB

-- Closure: term + environment
record Closure : Set where
  inductive
  constructor _↦_
  field
    term : TermB
    env  : List Closure
open Closure public

Stack = List Closure
ConfigK = Closure × Stack

-- lookup in the environment
index : ℕ -> List Closure -> Closure
index zero (c ∷ _)    = c
index (suc n) (_ ∷ cs) = index n cs
index _ []             = var 0 ↦ []  -- fallback (represents a free variable)

data _-≻_ : ConfigK → ConfigK → Set where
  AppK : {t u : TermB} → {ρ σ : Stack} →
         ((app t u) ↦ ρ , σ)
         -≻ ((t ↦ ρ) , (u ↦ ρ) ∷ σ)

  AbsK : {t : TermB} → {c : Closure} → {ρ σ : Stack} →
         ((lam t) ↦ ρ , c ∷ σ)
         -≻ ((t ↦ (c ∷ ρ)) , σ)

  VarK : {n : ℕ} → {ρ σ : Stack} →
         ((var n) ↦ ρ , σ)
         -≻ (index n ρ , σ)


iden1 : (app (lam (var zero)) (lam (var zero)) ↦ [] , []) -≻
        (((lam (var zero)) ↦ []) , ((lam (var zero)) ↦ []) ∷ [])
iden1 = AppK 

iden2 : (((lam (var zero)) ↦ []) , ((lam (var zero)) ↦ []) ∷ []) -≻
        ((var zero) ↦  (((lam (var zero)) ↦ []) ∷ []) , [])
iden2 = AbsK

iden3 : ((var zero) ↦  (((lam (var zero)) ↦ []) ∷ []) , []) -≻
        ((lam (var zero)) ↦ [] , [])
iden3 = VarK
