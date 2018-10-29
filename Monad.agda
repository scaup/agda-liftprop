module Monad where
-- open import Imports

open import Postulates

-- stdlib {{{

open import Data.Nat
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

-- "Typeclass" monad with monadic laws

record Monad (M : Set → Set) : Set₁ where
  field
    return : {X : Set} → X → M X
    _>>=_ : {X Y : Set} → (M X) → (X → M Y) → (M Y)
    leftId : {X Y : Set} → (f : X → M Y) → (x : X) →
             return x >>= f ≡ f x
    rightId : {X : Set} → (m : M X) →
              m >>= return ≡ m
    assoc : {X Y Z : Set} → (g : X → M Y) → (f : Y → M Z) → (mx : M X) →
            (mx >>= g) >>= f ≡ mx >>= (λ x → g x >>= f)

open Monad {{...}} public


_>>_ : {M : Set → Set} → {{ Mimp : Monad M }} → {X Y : Set} → M X → M Y → M Y
mx >> my = mx >>= λ _ → my

{-# DISPLAY Monad._>>=_ imp a b = a >>= b #-}
{-# DISPLAY Monad.return i a = return a #-}
{-# DISPLAY Monad.return i = return #-} -- f ∘ return

{-
mfilter : {A : Set} → {M : Set → Set} → {{ Mimp : Monad M }} → {P : A → Set} →
  (P? : Decidable P) → M A → M A
mfilter {A} {M} P? ma =
  ma >>= f
  where
    f : A → M A
    f a with P? a
    f a | yes p = {!!}
    f a | no ¬p = {!!}
-}


