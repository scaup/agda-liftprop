{-# OPTIONS --allow-unsolved-metas #-}

module Lift where

open import FunctorTC public

open import Postulates

-- stdlib {{{

open import Data.Product
open import Data.Unit
open import Data.Sum
open import Function

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- }}}

Predicate : (A : Set) → Set₁
Predicate A = A → Set

_∨_ : {A : Set} → Predicate A → Predicate A → Predicate A
(P ∨ Q) a = P a ⊎ Q a

_∧_ : {A : Set} → Predicate A → Predicate A → Predicate A
(P ∧ Q) a = P a × Q a

record Lift {A : Set} {F : Set → Set} {{ Fimp : Functor F }} (P : Predicate A) (monadicValue : F A) : Set where
  field
    witness : F (Σ[ x ∈ A ] P x)
    corresponds : monadicValue ≡ fmap proj₁ witness

open Lift public

nothing2Prove : {F : Set → Set} → {{ Fimp : Functor F }} →
                {A : Set} →
                (fa : F A) → Lift (const ⊤) fa
witness (nothing2Prove fa) = fmap (λ a → a , tt) fa
corresponds (nothing2Prove fa) = sym $
  begin
    fmap proj₁ (fmap (λ a → a , tt) fa)
  ≡⟨ sym $ composition _ _ _ ⟩
    fmap id fa
  ≡⟨ unit ⟩
    fa ∎

Res : {A B : Set} → (A → B) → (P : Predicate A) → (Σ A P → B)
Res {A} {B} f P = f ∘ proj₁

fmapR : ∀{F A B P} → {{_ : Functor F}} → {fa : F A} →
  (Σ A P → B) →
  (Lift P fa) →
  F B
fmapR f lp = fmap f (witness lp)

fmapRValid : ∀{F A B P} → {{fimp : Functor F}} → (fa : F A) →
  (Pfa : Lift P fa) →
  (fᵣ : Σ A P → B) →
  (f : A → B) →
  (Res f P ≡ fᵣ) →
  fmapR fᵣ Pfa ≡ fmap f fa
fmapRValid fa faLP fᵣ f proofR =
  begin
    fmapR fᵣ faLP
  ≡⟨ refl ⟩
    fmap fᵣ (witness faLP)
  ≡⟨ cong (flip fmap (witness faLP)) (sym proofR) ⟩
    fmap (f ∘ proj₁) (witness faLP)
  ≡⟨ composition _ _ _ ⟩
    fmap f (fmap proj₁ (witness faLP))
  ≡⟨ cong (fmap f) (sym (corresponds faLP)) ⟩
    fmap f fa ∎

implicationL : {F : Set → Set} → {{_ : Functor F}} →
               {A : Set} → {fa : F A } → {P Q : Predicate A} →
               ((a : A) → P a → Q a) →
               Lift P fa → Lift Q fa
witness (implicationL Imp Pfa) = fmapR (λ{(a , p) → a , Imp a p}) Pfa
corresponds (implicationL {A = A} {fa = fa} {P = P} {Q = Q} Imp Pfa) = sym $
  begin
    fmap proj₁ (fmap (λ {(a , p) → a , Imp a p}) (witness Pfa))
  ≡⟨ sym $ composition _ _ _ ⟩
    fmap (proj₁ {A = A} {B = Q} ∘ (λ {(a , p) → a , Imp a p})) (witness Pfa)
  ≡⟨ refl ⟩
    fmap proj₁ (witness Pfa)
  ≡⟨ sym $ corresponds Pfa ⟩
    fa ∎

LPOr : ∀{F A} → {{ _ : Functor F }} → {fa : F A} → {P Q : Predicate A} →
  Lift P fa ⊎ Lift Q fa → Lift (P ∨ Q) fa
LPOr (inj₁ pPfa) = implicationL (λ a x → inj₁ x) pPfa
LPOr (inj₂ pQfa) = implicationL (λ a x → inj₂ x) pQfa
