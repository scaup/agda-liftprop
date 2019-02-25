module Functors.IO where

open import FunctorTC


-- ioFunctor : Functor IO
-- ioFunctor = Applicative.functorM ioApplicative

postulate
  IO : Set → Set
  instance
    ioFunctor : Functor IO
