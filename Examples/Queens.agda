module Examples.Queens where

open import MonadTC
open import ApplicativeTC
open import FunctorTC
open import Monads.List
open import Applicatives.List
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

open import Examples.ListFunctions

open import Prelude
open Prelude.Integers

upto : ℕ → List ℕ
upto zero = []
upto (suc n) = range 0 n

toCoordinates : List ℕ → List (ℕ × ℕ)
toCoordinates qs = zip (upto (length qs)) qs

upwardDiagonal : ℕ × ℕ → ℤ
upwardDiagonal (x , y) = x - y

downwardDiagonal : ℕ × ℕ → ℕ
downwardDiagonal (x , y) = x + y

row : ℕ × ℕ → ℕ
row (x , y) = y

_areNotAttacking_ : List ℕ → ℕ → Bool
qs areNotAttacking q
  = upwardDiagonal qCoordinate ∉ fmap upwardDiagonal qsCoordinates
  && downwardDiagonal qCoordinate ∉ fmap downwardDiagonal qsCoordinates
  && row qCoordinate ∉ fmap row qsCoordinates
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
