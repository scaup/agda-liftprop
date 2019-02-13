module ApplicativeTC where

open import FunctorTC
open import Postulates

-- stdlib {{{

open import Function
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- }}}

record Applicative (A : Set → Set) : Set₁ where
  field
    {{functorM}} : Functor A
    pure : {X : Set} → X → A X
    _<*>_ : {X Y : Set} → A (X → Y) → A X → A Y
    homomorphism : {X Y : Set} → (f : X → Y) → (x : X) → pure f <*> (pure x) ≡ pure (f x)
    interchange : {X Y : Set} → (f : A (X → Y)) → (x : X) →
                  f <*> pure x ≡ pure (λ k → k x) <*> f
    compositionA : {X Y Z : Set} → (u : A (Y → Z)) → (v : A (X → Y)) → (w : A X) →
                   (u <*> (v <*> w)) ≡ (((pure (λ f g → f ∘ g) <*> u) <*> v) <*> w)
    compatiblefmapA : {X Y : Set} → {f : X → Y} → {ax : A X} →
                     fmap f ax ≡ pure f <*> ax


open Applicative {{...}} public

{-# DISPLAY Applicative._<*>_ a b = a <*> b #-}
