{-# OPTIONS --allow-unsolved-metas #-}

module Monads.IO where

open import Functors.IO
open import Applicatives.IO

open import MonadTC

-- postulate
  -- ioMonad : Monad IO


postulate
  _>>=IO_ : {X Y : Set} → IO X → (X → IO Y) → IO Y

instance
  ioMonad : Monad IO
  open Monad
  applicativeM ioMonad = ioApplicative
  _>>=_ ioMonad = _>>=IO_
  leftId ioMonad = {!!}
  rightId ioMonad = {!!}
  assoc ioMonad = {!!}
  compatible<*> ioMonad = {!!}
