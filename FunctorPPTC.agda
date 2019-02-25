module FunctorPPTC where

open import FunctorTC
open import FunctorLift
open import Postulates

open import Function
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

record FunctorPP (F : Set → Set) : Set₁ where
  field
    {{functorM}} : Functor F
    _,L_ : {X : Set} → {P Q : Predicate X} → {fx : F X} →
           Lift P fx → Lift Q fx → Lift (P ∧ Q) fx

open FunctorPP {{...}} public

open import Functors.List
open import Data.List

instance
  listPP : FunctorPP List
  open FunctorPP
  functorM listPP = listFunctor
  _,L_ listPP = Examples.ListFunctionsProofs._,L_
     where import Examples.ListFunctionsProofs
