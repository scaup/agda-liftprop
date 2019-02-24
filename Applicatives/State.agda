module Applicatives.State where

open import ApplicativeTC

open import FunctorTC
open import Functors.State

open import Function
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning

pureS : {S A : Set} → A → State S A
pureS a s = a , s

instance
  open Applicative
  stateApplicative : {S : Set} → Applicative (State S)
  functorM stateApplicative = stateFunctor
  pure stateApplicative = pureS
  _<*>_ stateApplicative kf k s₀ with kf s₀
  _<*>_ stateApplicative kf k s₀ | f , s₁ with k s₁
  _<*>_ stateApplicative kf k s₀ | f , s₁ | x , s₂ = f x , s₂
  homomorphism stateApplicative = λ f x → refl
  interchange stateApplicative = λ f x → refl
  compositionA stateApplicative = λ u v w → refl
  compatiblefmapA stateApplicative = refl
