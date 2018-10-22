module Hoare.Monad where

open import Monad.State

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

-- from 'The Hoare State Monad' by Wouter Swierstra

record StateHoare (S : Set) (A : Set) (P : A → S → S → Set) : Set where
  field
    runStateHoare : (s₁ : S) → Σ (A × S) λ{(a , s₂) → P a s₁ s₂}

open StateHoare public

returnStateHoare : {S A : Set} → (a : A) → StateHoare S A λ a' s₁ s₂ → s₁ ≡ s₂ × a' ≡ a
runStateHoare (returnStateHoare a) s₁ = (a , s₁) , refl , refl

_>>=StateHoare_ : ∀{A S B} →
          {P₁ : A → S → S → Set} →
          {P₂ : A → B → S → S → Set} →
          StateHoare S A P₁ →
          (f : (a : A) → StateHoare S B (P₂ a)) →
          StateHoare S B λ b s₁ s₃ → Σ[ a ∈ A ] Σ[ s₂ ∈ S ] P₁ a s₁ s₂ × P₂ a b s₂ s₃
runStateHoare (k >>=StateHoare f) s₁ with runStateHoare k s₁
runStateHoare (k >>=StateHoare f) s₁ | (a , s₂) , p₁as₁s₂ with runStateHoare (f a) s₂
runStateHoare (k >>=StateHoare f) s₁ | (a , s₂) , p₁as₁s₂ | (b , s₃) , p₂abs₂s₃ = (b , s₃) , a , s₂ , p₁as₁s₂ , p₂abs₂s₃

toStateHoare : ∀{S A} → (k : State S A) → StateHoare S A λ a s₁ s₂ → runState k s₁ ≡ (a , s₂)
runStateHoare (toStateHoare k) s = runState k s , refl

impStateHoare : ∀{S A P Q} → StateHoare S A P → (∀{a s₁ s₂} → (P a s₁ s₂) → (Q a s₁ s₂)) → StateHoare S A Q
runStateHoare (impStateHoare record { runStateHoare = k } imp) s₁ = (proj₁ (proj₁ (k s₁)) , proj₂ (proj₁ (k s₁))) , imp (proj₂ (k s₁))

_concluding_ = impStateHoare

forget : {A S : Set} → {P : A → S → S → Set} →
         StateHoare S A P → State S A
runState (forget record { runStateHoare = f }) s₀ with f s₀
runState (forget record { runStateHoare = f }) s₀ | (a , s₁) , p = (a , s₁)
-- runState (forget record { runStateHoare = f }) s₀ = proj₁ (f s₀)
