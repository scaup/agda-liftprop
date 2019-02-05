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
  stateFunctor : {S : Set} → Functor (State S)
  runState (Functor.fmap stateFunctor f record { runState = k }) s0 with k s0
  runState (Functor.fmap stateFunctor f record { runState = k }) s0 | x , s1 = f x , s1
  Functor.composition stateFunctor g f fa = refl
  Functor.unit stateFunctor = refl
