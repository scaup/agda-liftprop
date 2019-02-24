module Functors.State where

open import FunctorTC

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

State : Set → Set → Set
State S A = S → A × S

get : {S : Set} → State S S
get s = s , s

modify : {S : Set} → (S → S) → State S ⊤
modify f s = tt , f s

put : {S : Set} → S → State S ⊤
put s s' = tt , s

evalState : {A S : Set} → State S A → S → A
evalState k s = proj₁ (k s)

execState : {A S : Set} → State S A → S → S
execState k s = proj₂ (k s)

runState : {A S : Set} → State S A → S → A × S
runState = id

instance
  open Functor
  stateFunctor : ∀{S} → Functor (State S)
  fmap stateFunctor f k s₀ with k s₀
  fmap stateFunctor f k s₀ | x , s₁ = f x , s₁
  composition stateFunctor g f k = refl
  unit stateFunctor = refl
