{-# OPTIONS --allow-unsolved-metas #-}

module Monads.State where

open import MonadTC

open import Functors.State

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

instance
  stateMonad : {S : Set} → Monad (State S)
  runState (Monad.return stateMonad x) s = x , s
  runState ((stateMonad Monad.>>= record { runState = k }) f) s0 with k s0
  runState ((stateMonad Monad.>>= record { runState = k }) f) s0 | x , s1 = runState (f x) s1
  Monad.leftId stateMonad = {!!}
  Monad.rightId stateMonad = {!!}
  Monad.assoc stateMonad = {!!}
  Monad.functorM stateMonad = stateFunctor
  Monad.compatiblefmap stateMonad {X} {Y} {f} {k} = {!!}
