module FunctorTC where

open import Function
open import Relation.Binary.PropositionalEquality

record Functor (F : Set → Set) : Set₁ where
  field
    fmap : {X Y : Set} → (X → Y) → F X → F Y
    composition : {A B C : Set} → (g : A → B) → (f : B → C) → (fa : F A) →
                  fmap (f ∘ g) fa ≡ (fmap f ∘ fmap g) fa
    unit : {A : Set} → {fa : F A} → fmap {X = A} {Y = A} id fa ≡ fa

open Functor {{...}} public
