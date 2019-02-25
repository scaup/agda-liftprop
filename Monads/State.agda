module Monads.State where

open import MonadTC

open import Functors.State
open import Applicatives.State

open import Postulates

-- stdlib {{{

open import Data.Nat
open import Data.Bool hiding (_≟_; _∧_)
open import Data.Product
open import Data.Unit hiding (_≟_; _≤?_; _≤_)
open import Data.Empty
open import Data.Sum
open import Function

open import Relation.Unary using (Decidable)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- }}}

_>>=S_ : ∀{S A B} → State S A → (A → State S B) → State S B
(k >>=S f) s₀ with k s₀
(k >>=S f) s₀ | a , s₁ = f a s₁

instance
  open Monad
  stateMonad : {S : Set} → Monad (State S)
  Monad.applicativeM stateMonad = stateApplicative
  _>>=_ stateMonad = _>>=S_
  Monad.leftId stateMonad = λ f x → refl
  Monad.rightId stateMonad = λ m → refl
  Monad.assoc stateMonad = λ g f mx → refl
  Monad.compatible<*> stateMonad = λ mf mx → refl
