module Examples.ListFunctions where

open import FunctorTC
open import Functors.List

open import Data.Bool renaming (_∧_ to _&&_; _∨_ to _||_)
open import Data.List hiding (filter)
open import Data.Nat hiding (_≟_)
open import Data.Nat.Properties hiding (_≟_)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary

filter : {A : Set} → (A → Bool) → List A → List A
filter f [] = []
filter f (x ∷ xs) with f x ≟ true
filter f (x ∷ xs) | yes _ = x ∷ filter f xs
filter f (x ∷ xs) | no _ = filter f xs

range : ℕ → ℕ → List ℕ
range zero zero = [ 0 ]
range (suc n) zero = []
range zero (suc m) = range zero m ++ [ suc m ]
range (suc n) (suc m) = fmap suc (range n m)
