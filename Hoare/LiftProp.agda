{-# OPTIONS --allow-unsolved-metas #-}

module Hoare.LiftProp where

open import LiftProp
open import Monad.State
open import Hoare.Monad
open import Postulates

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

record LiftPropStateHoare {A S : Set} (P : A → S → S → Set) (stateComp : State S A) : Set where
  constructor ⟦_<>_⟧
  field
    stateCompX : StateHoare S A P
    proofPPE : stateComp ≡ forget stateCompX

open LiftPropStateHoare

open StateHoare {{...}}
open State {{...}}


_>>=StateHoareLP_ :
  {A B S : Set} →
  {P : A → S → S → Set} →
  {Q : A → B → S → S → Set} →
  {stateCompA : State S A} →
  {f : (a : A) → State S B} →
  LiftPropStateHoare P stateCompA →
  ((a : A) → LiftPropStateHoare (Q a) (f a)) →
  LiftPropStateHoare (λ b s₁ s₃ → Σ[ a ∈ A ] Σ[ s₂ ∈ S ] P a s₁ s₂ × Q a b s₂ s₃) (stateCompA >>= f)
stateCompX (⟦ stateCompAX <> proof ⟧ >>=StateHoareLP f) = stateCompAX >>=StateHoare λ a → stateCompX (f a)
proofPPE (_>>=StateHoareLP_ {A = A} {B = B} {S = S} {stateCompA = stateCompA} {f = f} ⟦ stateCompAX <> proof ⟧ g) =
  begin
    stateCompA >>= f
  ≡⟨ cong (flip _>>=_ f) proof ⟩
    forget stateCompAX >>= f
  ≡⟨ {!!} ⟩
    forget (stateCompAX >>=StateHoare (stateCompX ∘ g)) ∎

returnStateHoareLP :
  {S A : Set} →
  (a : A) →
  LiftPropStateHoare (λ a' s₁ s₂ → s₁ ≡ s₂ × a' ≡ a) (return {State S} a)
returnStateHoareLP a = ⟦ returnStateHoare a <> refl ⟧

impStateHoareLP :
  ∀{S A P Q} →
  {stateCompA : State S A} →
  LiftPropStateHoare P stateCompA →
  (∀{a s₁ s₂} → (P a s₁ s₂) → (Q a s₁ s₂)) →
  LiftPropStateHoare Q stateCompA
impStateHoareLP ⟦ stateCompX₁ <> proofPPE₁ ⟧ imp = {!!}

_⇒_ = impStateHoareLP

toStateHoareLP : ∀{S A} →
  (k : State S A) →
  LiftPropStateHoare (λ a s₁ s₂ → runState k s₁ ≡ (a , s₂)) k
toStateHoareLP k = ⟦ (toStateHoare k) <> refl ⟧
