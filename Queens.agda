module Queens where

open import Monad.List
open import Monad
open import LiftProp
open import LiftProp.List


-- stdlib {{{

open import Data.Nat
open import Data.List
open import Data.Bool hiding (_≟_; _∧_)
open import Data.Product
open import Data.Unit hiding (_≟_; _≤?_; _≤_)
open import Data.Empty
open import Data.Sum
open import Function

open import Relation.Unary using (Decidable)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

-- }}}

-- helper functions {{{

p₁ = proj₁
p₂ = proj₂

_∈_ : {A : Set} → A → List A → Set
a ∈ [] = ⊥
a ∈ (x ∷ xs) = a ≡ x ⊎ (a ∈ xs)

_∈?_ : (a : ℕ) → (xs : List ℕ) → Dec (a ∈ xs)
a ∈? [] = no id
a ∈? (x ∷ xs) with a ≟ x
(a ∈? (x ∷ xs)) | yes p = yes (inj₁ p)
(a ∈? (x ∷ xs)) | no ¬p with a ∈? xs
(a ∈? (x ∷ xs)) | no ¬p | yes p = yes (inj₂ p)
(a ∈? (x ∷ xs)) | no ¬p | no ¬p₁ = no σ
  where
    σ : ¬ (a ≡ x ⊎ (a ∈ xs))
    σ (inj₁ x) = ¬p x
    σ (inj₂ y) = ¬p₁ y

decNegProp : (P : Set) → Dec P → Dec (¬ P)
decNegProp P (yes p) = no λ z → z p
decNegProp P (no ¬p) = yes ¬p

_∉_ : {A : Set} → A → List A → Set
a ∉ xs = ¬ (a ∈ xs)

_∉?_ : (a : ℕ) → (xs : List ℕ) → Dec (a ∉ xs)
_∉?_ a xs = decNegProp (a ∈ xs) (a ∈? xs)

addX : List ℕ → List (ℕ × ℕ)
addX xs = f 0 (reverse xs)
  where
    f : ℕ → List ℕ → List (ℕ × ℕ)
    f n [] = []
    f n (x ∷ xs) = (n , x) ∷ f (suc n) xs

_-_ : ℕ → ℕ → ℕ
x - zero = x
zero - suc y = zero
suc x - suc y = x - y

-- }}}

{-

On a n×n chessboard, a list of length k (where each element is < n) represents a configuration of k queens, described as follows.
The queens are placed in the k leftmost columns.
The row of the i'th queen is determined by the i'th element in the list.

[1, 3, 0] represents the three queens as follows

0 Q 0 0
0 0 0 0
Q 0 0 0
0 0 Q 0

-}

_[_]AreNotAttacking_ : List ℕ → ℕ → ℕ → Set
qs [ n ]AreNotAttacking q
  = q ∉ qs
  × newDownwardDiagonal ∉ downwardDiagonals
  × newUpwardDiagonal ∉ upwardDiagonals
    where
      newDownwardDiagonal = q + length qs
      newUpwardDiagonal = length qs + n - q
      downwardDiagonals = fmap (λ{ (x , y) → x + y }) (addX qs)
      upwardDiagonals = fmap (λ{ (x , y) → (x + n) - y }) (addX qs)


PeacefulQueens : ℕ → List ℕ → Set
PeacefulQueens n [] = ⊤
PeacefulQueens n (x ∷ qs)
  = (PeacefulQueens n qs)
  × x < n
  × (qs [ n ]AreNotAttacking x)


_[_]AreNotAttacking?_ : (qs : List ℕ) → (n : ℕ) → (q : ℕ) → Dec (qs [ n ]AreNotAttacking q)
qs [ n ]AreNotAttacking? q = f (_ ∉? _ ) (f (_ ∉? _) (_ ∉? _))
  where
    f : {P : Set} → {Q : Set} → Dec P → Dec Q → Dec (P × Q)
    f (yes p) (yes p₁) = yes (p , p₁)
    f (yes p) (no ¬p) = no λ x → ¬p (proj₂ x)
    f (no ¬p) dq = no λ x → ¬p (proj₁ x)


queens : ℕ → ℕ → List (List ℕ)
queens n zero = [] ∷ []
queens n (suc k) =
  do
    qs ← queens n k
    q ← filter (λ q → qs [ n ]AreNotAttacking? q) (range n)
    return (q ∷ qs)


_↑_ = _∧LPlist_

queensProven : (n : ℕ) → (k : ℕ) → LiftProp.LiftProp (PeacefulQueens n) (queens n k)
queensProven n zero = ⟦ (([] , tt) ∷ []) <> refl ⟧
queensProven n (suc k) =
  let
    _>>=_ = _>>=LP_
    return = returnLP
  in
  do
    (qs , pqspf) ← queensProven n k
    (q , (pqsnaq , pq<n)) ← filterNewLP _ (range n)
                          ↑ filterPreservesLP _ (rangeLP n)
    return (q ∷ qs , pqspf , pq<n , pqsnaq)


-- alternative {{{

NoDup : List ℕ → Set
NoDup [] = ⊤
NoDup (x ∷ xs) = x ∉ xs × NoDup xs

QueensLivePeacefully : ℕ → List ℕ → Set
QueensLivePeacefully n qs
  = LiftProp (λ q → q < n) qs
  × NoDup qs
  × NoDup downwardDiagonals
  × NoDup upwardDiagonals
    where
      downwardDiagonals = fmap (λ{ (x , y) → x + y }) (addX qs)
      upwardDiagonals = fmap (λ{ (x , y) → (x + n) - y }) (addX qs)

queensProvenPeacefully : (n : ℕ) → (k : ℕ) → LiftProp (QueensLivePeacefully n) (queens n k)
queensProvenPeacefully n zero = {!!}
queensProvenPeacefully n (suc k) =
  let
    _>>=_ = _>>=LP_
    return = returnLP
  in
  do
    (qs , qs<n , qsNoDup , qsNoDupUD , qsNoDupDD) ← queensProvenPeacefully n k
    (q , ((pq∉qs , qNotOnDDqs , qNotOnUDqs) , pq<n)) ← filterNewLP _ (range n)
                   ↑ filterPreservesLP _ (rangeLP n)
    return (q ∷ qs , ((q , pq<n) ∷LP qs<n) , (pq∉qs , qsNoDup) , {!!} , {!!})

-- }}}
