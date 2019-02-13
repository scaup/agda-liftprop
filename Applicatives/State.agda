{-# OPTIONS --allow-unsolved-metas #-}

module Applicatives.State where

open import ApplicativeTC

open import FunctorTC
open import Functors.State

open import Function
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning

instance
  stateApplicative : {S : Set} → Applicative (State S)
  Applicative.functorM stateApplicative = stateFunctor
  runState (Applicative.pure stateApplicative x) s = x , s
  runState ((stateApplicative Applicative.<*> sf) sx) = {!!}
  Applicative.homomorphism stateApplicative = {!!}
  Applicative.interchange stateApplicative = {!!}
  Applicative.compositionA stateApplicative = {!!}
  Applicative.compatiblefmapA stateApplicative = {!!}
