module Monad.State where

-- open import Imports

open import Monad public
open import Data.Product
open import Data.Unit

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

record State (S A : Set) : Set where
  field
    runState : S → A × S

open State public

evalState : ∀{S A} → State S A → S → A
evalState record { runState = k } s = proj₁ $ k s

execState : ∀{S A} → State S A → S → S
execState record { runState = k } s = proj₂ $ k s

get : {S : Set} → State S S
runState get s = s , s

modify : {S : Set} → (S → S) → State S ⊤
runState (modify f) s = tt , f s

put : {S : Set} → S → State S ⊤
runState (put s) s' = tt , s

instance
  stateMonad : {S : Set} → Monad (State S)
  runState (Monad.return stateMonad x) s = x , s
  runState ((stateMonad Monad.>>= record { runState = k }) f) s with k s
  runState ((stateMonad Monad.>>= record { runState = k }) f) s | x , s' with f x
  runState ((stateMonad Monad.>>= record { runState = k }) f) s | x , s' | record { runState = k2 } = k2 s'
  Monad.leftId stateMonad f x = refl
  Monad.rightId stateMonad k = refl
  Monad.assoc stateMonad f g k = refl
