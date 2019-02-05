{-# OPTIONS --allow-unsolved-metas #-}

module Applicatives.List where

open import ApplicativeTC

open import FunctorTC
open import Functors.List

open import Data.List
open import Data.List.Properties
open import Relation.Binary.PropositionalEquality hiding ([_])

instance
  listApplicative : Applicative List
  Applicative.pure listApplicative x = [ x ]
  (listApplicative Applicative.<*> []) xs = []
  (listApplicative Applicative.<*> (f ∷ fs)) xs = fmap f xs ++ (fs <*> xs)
  Applicative.identity listApplicative = {!!}
  Applicative.homomorphism listApplicative = {!!}
  Applicative.interchange listApplicative = {!!}
  Applicative.compositionA listApplicative = {!!}
  Applicative.functorM listApplicative = listFunctor
  Applicative.compatiblefmapA listApplicative = {!!}
