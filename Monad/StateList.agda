module Monad.StateList where

open import Monad public
open import Imports
open import Monad.List


record StateList (S A : Set) : Set where
  field
    runStateList : (S → List (A × S))

open StateList public

instance
  statelistMonad : {S : Set} → Monad (StateList S)
  runStateList (Monad.return statelistMonad x) s = (x , s) ∷ []
  runStateList ((statelistMonad Monad.>>= record { runStateList = k }) f) s = concat (fmap (λ{(x , s') → runStateList (f x) s'}) (k s))
  Monad.leftId statelistMonad f x = {!!}
  Monad.rightId statelistMonad m = {!!}
  Monad.assoc statelistMonad g f mx = {!!}
