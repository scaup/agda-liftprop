module Monad.Cont where

open import Monad public
open import Imports

record Cont (C A : Set) : Set where
  field
    runCont : (A → C) → C

open Cont public

instance
  contMonad : {C : Set} → Monad (Cont C)
  runCont (Monad.return contMonad x) f = f x
  runCont ((contMonad Monad.>>= record { runCont = cx }) f) y2c = cx (λ x → runCont (f x) y2c)
  Monad.leftId contMonad f x = refl
  Monad.rightId contMonad m = refl
  Monad.assoc contMonad g f mx = refl
