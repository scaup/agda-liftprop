module FunctorCombineLiftTC where

open import FunctorTC
open import Lift
open import Postulates

-- stdlib {{{

open import Function
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- }}}

record FunctorPreserving (F : Set → Set) : Set₁ where
  field
    {{functorM}} : Functor F
    _,L_ : {X : Set} → {P₁ P₂ : Predicate X} → {fx : F X} →
           Lift P₁ fx → Lift P₂ fx → Lift (P₁ ∧ P₂) fx

  -- preserves pullbacks property
  --....

open FunctorPreserving {{...}} public
