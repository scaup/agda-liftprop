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

fmapRValid : ∀{F A B P} → {{_ : Functor F}} → (fa : F A) →
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

fmapL' : ∀{F} → {{_ : Functor F}} → {A B : Set} →
  {P : Predicate A} → {Q : Predicate B} →
  {as : F A} → {f : A → B} →
  ({a : A} → P a → Q (f a)) → Lift P as → Lift Q (fmap f as)
witness (fmapL' {f = f} fL asP) = fmapR (λ{(a , p) → f a , fL p}) asP
corresponds (fmapL' {f = f} fL asP) = sym $
  begin
    fmap proj₁ (fmap (λ { (a , p) → f a , fL p }) (witness asP))
  ≡⟨ sym $ composition _ _ _ ⟩
    fmap (f ∘ proj₁) (witness asP)
  ≡⟨ composition _ _ _ ⟩
    fmap f (fmap proj₁ (witness asP))
  ≡⟨ cong (fmap f) (sym $ corresponds asP) ⟩
    fmap f _ ∎

subsL : {F : Set → Set} → {{_ : Functor F}} →
        {A : Set} → {fa₁ fa₂ : F A } → {P : Predicate A} →
          fa₁ ≡ fa₂ → Lift P fa₁ → Lift P fa₂
subsL refl = id

applyL : {F : Set → Set} → {{_ : Functor F}} →
              {A : Set} → {fa : F A } → {P Q : Predicate A} →
              ({a : A} → P a → Q a) →
              Lift P fa → Lift Q fa
applyL {fa = fa} imp lp = subsL unit (fmapL' {f = id} imp lp)

LPOr : ∀{F A} → {{ _ : Functor F }} → {fa : F A} → {P Q : Predicate A} →
  Lift P fa ⊎ Lift Q fa → Lift (P ∨ Q) fa
LPOr (inj₁ pPfa) = applyL inj₁ pPfa
LPOr (inj₂ pQfa) = applyL inj₂ pQfa
