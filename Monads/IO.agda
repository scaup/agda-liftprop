module Monads.IO where

open import MonadTC
open import FunctorTC
open import Functors.IO

open import Postulates

-- stdlib {{{

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Agda.Builtin.IO public
open import Agda.Builtin.String public

-- }}}

instance
  ioMonad : Monad IO
  Monad.return ioMonad = returnIO
  Monad._>>=_ ioMonad = _>>=IO_
  Monad.leftId ioMonad = leftIdIO
  Monad.rightId ioMonad = rightIdIO
  Monad.assoc ioMonad = assocIO
  Monad.functorM ioMonad = ioFunctor
  Monad.compatiblefmap ioMonad = refl

{-# DISPLAY _>>=IO_ a b = a >>= b #-}
{-# DISPLAY returnIO = return #-}
