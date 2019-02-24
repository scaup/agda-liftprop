module Exp.HoareLift where

open import Functors.State using (State)
open import Monads.State renaming (_>>=S_ to _>>=_)
open import Applicatives.State renaming (pureS to return)
open import Data.Product
open import Exp.Hoare
open import Data.Product
open import Function

open import Postulates

open import Relation.Binary.PropositionalEquality public
open ≡-Reasoning

forget : ∀{S A P} → Hoare S A P → State S A
forget k = proj₁ ∘ k

record Lift {A S : Set} (P : A → S → S → Set) (k : State S A) : Set where
  field
    witness : Hoare S A P
    corresponds : k ≡ forget witness

open Lift

_>>=L_ : {A B S : Set} → {P : A → S → S → Set} → {Q : A → B → S → S → Set} →
  {k : State S A} → {f : (a : A) → State S B} →
  Lift P k → ((a : A) → Lift (Q a) (f a)) →
  Lift (λ b s₁ s₃ → Σ[ a ∈ A ] Σ[ s₂ ∈ S ] P a s₁ s₂ × Q a b s₂ s₃) (k >>= f)
witness (kP >>=L fP) = witness kP >>=H (witness ∘ fP)
corresponds (_>>=L_ {k = k} {f = f} kP fP) =
  begin
    k >>= f
  ≡⟨ cong (λ k → k >>= f) (corresponds kP) ⟩
    forget (witness kP) >>= f
  ≡⟨ cong (_>>=_ _) (funext λ a → corresponds (fP a)) ⟩
    forget (witness kP) >>= (forget ∘ witness ∘ fP)
  ≡⟨ refl ⟩
    forget (witness kP >>=H (witness ∘ fP)) ∎

returnL : {S A : Set} →
  (a : A) → Lift {A} {S} (λ a' s₂ s₃ → s₂ ≡ s₃ × a' ≡ a) (return a)
witness (returnL a) = returnH a
corresponds (returnL a) = refl

infixr 2 _⇒_

_⇒_ : ∀{S A P Q} → {k : State S A} →
     Lift P k →
     (∀{a s₁ s₂} → (P a s₁ s₂) → (Q a s₁ s₂)) →
     Lift Q k
witness (kP ⇒ imp) = witness kP ⇒H imp
corresponds (kP ⇒ imp) = corresponds kP

toL : ∀{S A} → (k : State S A) → Lift (λ a s₁ s₂ → k s₁ ≡ (a , s₂)) k
witness (toL k) = toHoare k
corresponds (toL k) = refl
