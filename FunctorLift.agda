open import FunctorTC
module FunctorLift {F : Set → Set} {{imp : Functor F}} where

open import Data.Unit using (⊤ ; tt) public
open import Data.Product public
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂) public
open import Function public
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning public

open import Prelude public

record Lift {A : Set} (P : Predicate A) (fa : F A) : Set where
  field
    witness : F (Σ A P)
    corresponds : fa ≡ fmap proj₁ witness

open Lift public

nothing2Prove : ∀{A} (fa : F A) → Lift (const ⊤) fa
witness (nothing2Prove fa) = fmap (λ a → a , tt) fa
corresponds (nothing2Prove fa) = sym $
  begin
    fmap proj₁ (fmap (λ a → a , tt) fa)
  ≡⟨ sym $ composition _ _ _ ⟩
    fmap id fa
  ≡⟨ unit ⟩
    fa ∎

fmapR : ∀{A B P} → {fa : F A} →
  (Σ A P → B) →
  (Lift P fa) →
  F B
fmapR f lp = fmap f (witness lp)

fmapRValid : ∀{A B P} → (fa : F A) →
  (Pfa : Lift P fa) →
  (fᵣ : Σ A P → B) →
  (f : A → B) →
  (Res P f ≡ fᵣ) →
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

fmapL : {A B : Set} → {P : Predicate A} → {Q : Predicate B} →
  {as : F A} → {f : A → B} →
  ({a : A} → P a → Q (f a)) → Lift P as → Lift Q (fmap f as)
witness (fmapL {f = f} fL asP) = fmapR (λ{(a , p) → f a , fL p}) asP
corresponds (fmapL {f = f} fL asP) = sym $
  begin
    fmap proj₁ (fmap (λ { (a , p) → f a , fL p }) (witness asP))
  ≡⟨ sym $ composition _ _ _ ⟩
    fmap (f ∘ proj₁) (witness asP)
  ≡⟨ composition _ _ _ ⟩
    fmap f (fmap proj₁ (witness asP))
  ≡⟨ cong (fmap f) (sym $ corresponds asP) ⟩
    fmap f _ ∎

subsL : {A : Set} → {fa₁ fa₂ : F A } → {P : Predicate A} →
          fa₁ ≡ fa₂ → Lift P fa₁ → Lift P fa₂
subsL refl = id

applyL : {A : Set} → {fa : F A } → {P Q : Predicate A} →
          ({a : A} → P a → Q a) → Lift P fa → Lift Q fa
applyL {fa = fa} imp lp = subsL unit (fmapL {f = id} imp lp)

moveQOutL : {A : Set} → {fa : F A } →
              {R : Set} → {P : R → A → Set} →
              Lift (λ a → (r : R) → P r a) fa →
              ((r : R) → Lift (P r) fa)
moveQOutL lp r = applyL (λ x → x r) (lp)

LPOr : ∀{A} → {fa : F A} → {P Q : Predicate A} →
  Lift P fa ⊎ Lift Q fa → Lift (P ∨ Q) fa
LPOr (inj₁ pPfa) = applyL inj₁ pPfa
LPOr (inj₂ pQfa) = applyL inj₂ pQfa

splitL : {A : Set} → {fa : F A} → {P Q : Predicate A} →
          Lift (P ∧ Q) fa → Lift P fa × Lift Q fa
proj₁ (splitL pqfa) = applyL proj₁ pqfa
proj₂ (splitL pqfa) = applyL proj₂ pqfa
