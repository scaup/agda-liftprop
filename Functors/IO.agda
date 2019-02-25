module Functors.IO where

open import FunctorTC

postulate
  IO : Set → Set
  instance
    ioFunctor : Functor IO
