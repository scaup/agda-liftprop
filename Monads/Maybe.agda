module Monad.Maybe where

open import Monad public
open import Imports

instance
  maybeMonad : Monad Maybe
  Monad.return maybeMonad x = just x
  Monad._>>=_ maybeMonad (just x) f = f x
  Monad._>>=_ maybeMonad nothing f = nothing
  Monad.leftId maybeMonad f x = refl
  Monad.rightId maybeMonad (just x) = refl
  Monad.rightId maybeMonad nothing = refl
  Monad.assoc maybeMonad f g (just x) = refl
  Monad.assoc maybeMonad f g nothing = refl
