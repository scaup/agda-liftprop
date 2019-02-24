module Applicatives.Cont where

open import ApplicativeTC


open import Functors.Cont
open import FunctorTC

open import Relation.Binary.PropositionalEquality
open import Function
open import Postulates

instance
  contApplicative : ∀{C} → Applicative (Cont C)
  open Applicative
  functorM contApplicative = contFunctor
  pure contApplicative = _|>_
  _<*>_ contApplicative cf cx = λ yc → cf (λ xy → fmap xy cx yc)
  homomorphism contApplicative f x = refl
  interchange contApplicative cf x = refl
  compositionA contApplicative = λ u v w → refl
  compatiblefmapA contApplicative = refl


postulate
  X Y C : Set
  cx : Cont C X
  cf : Cont C (X → Y)


