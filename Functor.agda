module Functor where

-- stdlib {{{

open import Data.Nat
open import Postulates
open import Data.List
open import Data.Bool hiding (_≟_; _∧_)
open import Data.Product
open import Data.Unit hiding (_≟_; _≤?_; _≤_)
open import Data.Empty
open import Data.Sum
open import Function

open import Relation.Unary using (Decidable)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- }}}

record Functor (F : Set → Set) : Set₁ where
  field
    fmap : {X Y : Set} → (X → Y) → F X → F Y
    composition : {A B C : Set} → (g : A → B) → (f : B → C) → (fa : F A) →
                  fmap (f ∘ g) fa ≡ (fmap f ∘ fmap g) fa
    unit : {A : Set} → {fa : F A} → fmap {X = A} {Y = A} id fa ≡ fa


open Functor {{...}} public

