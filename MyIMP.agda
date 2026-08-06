open import Data.String renaming (_++_ to _app_ ; _≟_ to _==S_) 
open import Data.List
open import Data.Product
open import Data.Nat using (ℕ ; _+_ ; _*_ ; _%_ ; suc ; _/_)
  renaming (_≟_ to _==ℕ_)
open import Relation.Nullary
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; _≢_)
open import Data.Fin
open import Data.List.Properties
open import Data.Maybe
open import Data.Bool

Id : Set
Id = String

data V : Set where
  Null : V
  nil : V
  op1V : ℕ → V → V
  op2V : ℕ → V → V → V

data E : Set where
  cnst : V → E
  var : Id → E
  op1E : ℕ → E → E
  op2E : ℕ → E → E → E




P : Set
data I : Set


P = List I

data I  where
  _:=_ : Id → E → I
  case_of_ : Id → List (E × P) → I
  while_is_ : Id → List (E × P) → I
  pop : I
  local : Id → P → I

-- \MCM
𝓜 : Set
𝓜 = List (Id × V)

-- lookup
eval-var : Id → 𝓜 → V
eval-var _ [] = Null
eval-var x ((y , v) ∷ vs) with x ==S y
...                         | yes _ = v
...                         | no _ = eval-var x vs

eval-expr : E → 𝓜 → V
eval-expr (cnst v) _ = v
eval-expr (var x) m = eval-var x m
eval-expr (op1E n e) m = op1V n (eval-expr e m)
eval-expr (op2E n e1 e2) m = op2V n (eval-expr e1 m) (eval-expr e2 m)

update : Id → V → 𝓜 → 𝓜
update _ _ [] = []
update x v1 ((y , v2) ∷ ms) with x ==S y
...                           | yes _ = (x , v1) ∷ ms
...                           | no _ = (y , v2) ∷ update x v1 ms


_≟V_ : (v1 v2 : V) → Bool
Null ≟V Null = true
nil ≟V nil = true
op1V n1 e1 ≟V op1V n2 e2 with n1 ==ℕ n2
...                       | yes _ = e1 ≟V e2
...                       | no _ = false
op2V n1 e1 e2 ≟V op2V n2 r1 r2 with n1 ==ℕ n2
...                             | yes _ = (e1 ≟V r1) ∧ (e2 ≟V r2)
...                             | no _ = false
_ ≟V _ = false




select : Id → 𝓜 → List (E × P) → Maybe ((List (E × V)) × P)
select _ _ [] = nothing
select x m ((cnst v , p) ∷ eps) with (eval-var x m) ≟V v
...                             | true = just ([] , p)
...                             | false = select x m eps
select x m (((op1E n (var y)) , p) ∷ eps) with eval-var x m
...                          | op1V n v = {!just ([(y , v)] , p)!}
...                          | _  = select x m eps
select _ _ _ = {!!}

-- \t
data _▸_ : (P × 𝓜) → (P × 𝓜) → Set where
  local-I : {x : Id} → {p1 p2 : P} → {m : 𝓜} →
    (((local x p1) ∷ p2) , m) ▸ (p1 ++ (pop ∷ p2) , (x , Null) ∷ m)
  pop-I : {p : P} → {h : Id × V} → {m : 𝓜} →
        (pop ∷ p , h ∷ m) ▸ (p , m)
  atr-I : {x : Id} → {e : E} → {p : P} → {m : 𝓜} →
        (((x := e) ∷ p) , m) ▸ (p , update x (eval-expr e m) m)
  --case-I : ((case x is b) ∷ p , m) ▸ () 

{-
-- \MCM
𝓜 : ℕ → Set
𝓜 n = List (Id × LΣQ n)



eval-var : {n : ℕ} → Id → 𝓜 n → LΣQ n
eval-var _ [] = []
eval-var x ((y , n) ∷ t) with ( x ==S y )
...        | yes _  = n 
...        | no _ = eval-var x t


eval : {n : ℕ} → E n → 𝓜 n → LΣQ n
eval (cnst n) _ = n
eval (var x) m = eval-var x m
eval (he e1) m with (eval e1 m)
...         | [] = []
...         | h ∷ t = [ h ]
eval (ta e1) m with (eval e1 m)
...         | [] = []
...         | h ∷ t = t
eval (con e1 e2) m = (eval e1 m) ++ (eval e2 m)


update : {n : ℕ} → Id → LΣQ n → 𝓜 n → 𝓜 n
update _ _ [] = []
update x n ((y , m) ∷ t) with x ==S y
...          | yes _ = (y , n) ∷ t
...          | no _ = (y , m) ∷ (update x n t)


listFin≟ :
  ∀ {n} →
  (xs ys : List (Fin n)) →
  Dec (xs ≡ ys)
listFin≟ = ≡-dec (_≟_)


select : {n : ℕ} → 𝓜 n → Id → List (E n × P n) → P n
select _ _ [] = []
select m x ((e , p) ∷ t) with listFin≟ (eval-var x m) (eval e m)
...                   | yes _ = p
...                   | no _ = select m x t


-- \t
data ►(n : ℕ) : 𝓜 n × P n → 𝓜 n × P n → Set where
  atr : {m : 𝓜 n} → {x : Id} → {e : E n} → {p : P n} → 
    ► n (m , ((x := e) ∷ p)) ((update  x (eval e m) m) , p)
  sel : {m : 𝓜 n} → {x : Id} → {b : List (E n × P n)} → {p : P n} → 
    ► n (m , ((case x of b) ∷ p)) (m , (select m x b) ++ p)
  loop-fin : {m : 𝓜 n} → {x : Id} → {b : List (E n × P n)} → {p : P n} →
     (select m x b) ≡ [] →
    ► n (m , ((while x is b) ∷ p)) (m , p)
  loop : {m : 𝓜 n} → {x : Id} → {b : List (E n × P n)} → {p : P n} →
     (select m x b) ≢ [] →
    ► n (m , ((while x is b) ∷ p)) (m , ((select m x b) ++ (while x is b) ∷ p))


-}
