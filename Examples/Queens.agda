module Examples.Queens where

open import MonadTC
open import ApplicativeTC
open import FunctorTC
open import Monads.List
open import Applicatives.List
open import Functors.List

open import Prelude
open Prelude.Integers
open Prelude.Booleans

open import Data.List hiding (filter)
open import Data.Product hiding (zip)
open import Examples.ListFunctions

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

QConfig = List ℕ

_areNotAttacking_ : QConfig → ℕ → Bool
qs areNotAttacking q
  = upwardDiagonal qCoordinate ∉ fmap upwardDiagonal qsCoordinates
  && downwardDiagonal qCoordinate ∉ fmap downwardDiagonal qsCoordinates
  && row qCoordinate ∉ fmap row qsCoordinates
    where
      qsCoordinates : List (ℕ × ℕ)
      qsCoordinates = zip (upto (length qs)) qs
      qCoordinate : ℕ × ℕ
      qCoordinate = length qs , q

queenConfigs : ℕ → ℕ → List QConfig
queenConfigs n zero = return []
queenConfigs n (suc k) =
  do
    qs ← queenConfigs n k
    q ← filter (λ q → qs areNotAttacking q) (range 0 (pred n))
    return (qs ++ [ q ])
