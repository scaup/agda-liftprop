{-# OPTIONS --allow-unsolved-metas #-}

module Functors.List where

open import FunctorTC

open import Data.List

instance
  listFunctor : Functor List
  Functor.fmap listFunctor f [] = []
  Functor.fmap listFunctor f (x ∷ xs) = f x ∷ fmap f xs
  Functor.composition listFunctor g f fa = {!!}
  Functor.unit listFunctor = {!!}
