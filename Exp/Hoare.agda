module Exp.Hoare where

-- open import Functors.State
open import Functors.State

-- stdlib {{{

open import Data.Nat
open import Data.Bool hiding (_≟_; _∧_; _∨_)
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


{-
-- OVERVIEW
+----------------+-------------+-----+
|                | General     |     |
+----------------+-------------+-----+
|                |             |     |
+----------------+-------------+-----+
|                |             |     |
+----------------+-------------+-----+
|                |             |     |
+----------------+-------------+-----+
-}

-- from 'The Hoare State Monad' by Wouter Swierstra

Hoare : (S : Set) (A : Set) (P : A → S → S → Set) → Set
Hoare S A P = (s₂ : S) → Σ (A × S) λ{(a , s₃) → P a s₂ s₃}

returnH : {S A : Set} → (a : A) → Hoare S A (λ a' s₂ s₃ → s₂ ≡ s₃ × a' ≡ a)
(returnH a) s₂ = (a , s₂) , refl , refl

_>>=H_ : ∀{A S B} → {P : A → S → S → Set} → {Q : A → B → S → S → Set} →
          Hoare S A P → (f : (a : A) → Hoare S B (Q a)) →
          Hoare S B (λ b s₁ s₃ → Σ[ a ∈ A ] Σ[ s₂ ∈ S ] P a s₁ s₂ × Q a b s₂ s₃)
(k >>=H f) s₁ with k s₁
(k >>=H f) s₁ | (a , s₂) , pas₁s₂ with f a s₂
(k >>=H f) s₁ | (a , s₂) , pas₁s₂ | (b , s₃) , qbs₂s₃ = (b , s₃) , a , s₂ , pas₁s₂ , qbs₂s₃

_⇒H_ : ∀{S A P Q} →
      Hoare S A P →
      (∀{a s₁ s₂} → (P a s₁ s₂) → (Q a s₁ s₂)) →
      Hoare S A Q
(k ⇒H imp) s₁ with k s₁
(k ⇒H imp) s₁ | (a , s₂) , p = (a , s₂) , imp p

toHoare : ∀{S A} → (k : State S A) → Hoare S A λ a s₀ s₁ → k s₀ ≡ (a , s₁)
toHoare k s₀ = (k s₀) , refl
