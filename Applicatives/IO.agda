{-# OPTIONS --allow-unsolved-metas #-}

module Applicatives.IO where

open import ApplicativeTC

-- postulate
  -- instance
    -- ioApplicative : Applicative IO

open import Functors.IO

postulate
  pureIO : {X : Set} → X → IO X


instance
  ioApplicative : Applicative IO
  open Applicative
  functorM ioApplicative = ioFunctor
  pure ioApplicative = pureIO
  _<*>_ ioApplicative = {!!}
  homomorphism ioApplicative = {!!}
  interchange ioApplicative = {!!}
  compositionA ioApplicative = {!!}
  compatiblefmapA ioApplicative = {!!}

