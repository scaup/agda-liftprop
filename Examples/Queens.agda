module Examples.Queens where

open import MonadTC
open import FunctorTC
open import Monads.List
open import Lift
open import Functors.List

-- stdlib {{{

open import Data.Nat renaming (_≟_ to _≟ℕ_)
open import Data.Integer renaming (_≟_ to _≟ℤ_ ; _-_ to _-ℤ_ ; _⊖_ to _-_ ; _+_ to _+ℤ_ ; _<_ to _<ℤ_)
open import Data.List hiding (filter)
open import Data.Bool hiding (_≟_) renaming (_∧_ to _&&_; _∨_ to _||_)
open import Data.Product hiding (zip)
open import Data.Unit hiding (_≟_; _≤?_; _≤_)
open import Data.Empty
open import Data.Sum
open import Function

open import Relation.Unary using (Decidable)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding ([_])

-- }}}

-- uninteresting {{{

record Eq {a} (A : Set a) : Set a where
  field
    _==_ : A → A → Bool

open Eq {{...}} public

instance
  eqNat : Eq ℕ
  Eq._==_ eqNat a b with a ≟ℕ b
  (eqNat Eq.== a) b | yes p = true
  (eqNat Eq.== a) b | no ¬p = false

  eqInt : Eq ℤ
  Eq._==_ eqInt a b with a ≟ℤ b
  (eqInt Eq.== a) b | yes p = true
  (eqInt Eq.== a) b | no ¬p = false

elem : {A : Set} → {{ _ : Eq A}} → A → List A → Bool
elem a [] = false
elem a (x ∷ as) = x == a || elem a as

_¬elem_ : {A : Set} → {{ _ : Eq A }} → A → List A → Bool
a ¬elem as = not (elem a as)

nodup : {A : Set} → {{ _ : Eq A}} → List A → Bool
nodup [] = true
nodup (x ∷ xs) = not (elem x xs) && nodup xs

-- }}}


test = (5 - 1) == (0 - 5)

upto : ℕ → List ℕ
upto zero = []
upto (suc n) = range 0 n

toCoordinates : List ℕ → List (ℕ × ℕ)
toCoordinates qs = zip (upto (length qs)) qs

{-
isPeaceful : List ℕ → Bool
isPeaceful qs = nodup (fmap toUpwardDiagonal coordinates) &&
                nodup (fmap toDownwardDiagonal coordinates) &&
                nodup (fmap toRow coordinates)
    where
      coordinates : List (ℕ × ℕ)
      coordinates = toCoordinates qs
      toUpwardDiagonal : ℕ × ℕ → ℕ
      toUpwardDiagonal (x , y) = x + y
      toDownwardDiagonal : ℕ × ℕ → ℤ
      toDownwardDiagonal (x , y) = x - y
      toRow : ℕ × ℕ → ℕ
      toRow (x , y) = y
-}

upwardDiagonal : ℕ × ℕ → ℤ
upwardDiagonal (x , y) = x - y

downwardDiagonal : ℕ × ℕ → ℕ
downwardDiagonal (x , y) = x + y

row : ℕ × ℕ → ℕ
row (x , y) = y

_areNotAttacking_ : List ℕ → ℕ → Bool
qs areNotAttacking q
  = upwardDiagonal qCoordinate ¬elem fmap upwardDiagonal qsCoordinates
  && downwardDiagonal qCoordinate ¬elem fmap downwardDiagonal qsCoordinates
  && row qCoordinate ¬elem fmap row qsCoordinates
    where
      qsCoordinates : List (ℕ × ℕ)
      qsCoordinates = zip (upto (length qs)) qs
      qCoordinate : ℕ × ℕ
      qCoordinate = length qs , q

queens : ℕ → ℕ → List (List ℕ)
queens n zero = return []
queens n (suc k) =
  do
    qs ← queens n k
    q ← filter (λ q → qs areNotAttacking q) (upto n)
    return (qs ++ [ q ])
