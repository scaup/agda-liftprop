module Functors.Cont where

open import FunctorTC

open import Function
open import Relation.Binary.PropositionalEquality

Cont : Set → Set → Set
Cont C A = (A → C) → C


instance
  contFunctor : ∀{C} → Functor (Cont C)
  open Functor
  fmap contFunctor f c k = c (k ∘ f)
  composition contFunctor f g c = refl
  unit contFunctor = refl
