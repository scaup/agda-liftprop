module ApplicativeTC where

open import FunctorTC public

open import Function
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

record Applicative (F : Set → Set) : Set₁ where
  field
    {{functorM}} : Functor F
    pure : {X : Set} → X → F X
    _<*>_ : {X Y : Set} → F (X → Y) → F X → F Y
    homomorphism : {X Y : Set} → (f : X → Y) → (x : X) → fmap f (pure x) ≡ pure (f x)
    interchange : {X Y : Set} → (f : F (X → Y)) → (x : X) →
                  f <*> pure x ≡ fmap (λ k → k x) f
    compositionA : {X Y Z : Set} → (u : F (Y → Z)) → (v : F (X → Y)) → (w : F X) →
                   (u <*> (v <*> w)) ≡ (((fmap (λ f g → f ∘ g) u) <*> v) <*> w)
    compatiblefmapA : {X Y : Set} → {f : X → Y} → {ax : F X} →
                     fmap f ax ≡ pure f <*> ax

  move : {X Y Z : Set} → (k : Y → Z) → (af : F (X → Y)) → (ax : F X) →
          fmap k (af <*> ax) ≡ fmap (λ x2y → k ∘ x2y) af <*> ax
  move k af ax =
    begin
      fmap k (af <*> ax)
    ≡⟨ compatiblefmapA ⟩
      pure k <*> (af <*> ax)
    ≡⟨ compositionA _ af ax ⟩
      ((fmap (λ f g → f ∘ g) (pure k)) <*> af) <*> ax
    ≡⟨ cong (flip _<*>_ _) (cong (flip _<*>_ _) (homomorphism _ _)) ⟩
      (pure ((λ f g → f ∘ g) k) <*> af) <*> ax
    ≡⟨ refl ⟩
      (pure ((λ f → k ∘ f)) <*> af) <*> ax
    ≡⟨ cong (flip _<*>_ _) (sym compatiblefmapA ) ⟩
      fmap (λ x2y → k ∘ x2y) af <*> ax ∎

  move' : {X Y Z : Set} →
          (k : X → Y) → (af : F (Y → Z)) → (ax : F X) →
          fmap (λ f → f ∘ k) af <*> ax ≡ af <*> fmap k ax
  move' k af ax =
    begin
      fmap (λ f → f ∘ k) af <*> ax
    ≡⟨ refl ⟩
      fmap ((λ z → z k) ∘ (λ f g x → f (g x))) af <*> ax
    ≡⟨ cong (flip _<*>_ _) (composition (λ f g x → f (g x)) (λ z → z k) af) ⟩
      fmap (λ z → z k) (fmap (λ f g → f ∘ g) af) <*> ax
    ≡⟨ cong (flip _<*>_ _) (sym $ interchange _ _) ⟩
      ((fmap (λ f g → f ∘ g) af) <*> pure k) <*> ax
    ≡⟨ sym (compositionA _ _ _) ⟩
      af <*> (pure k <*> ax)
    ≡⟨ cong (_<*>_ _) (sym compatiblefmapA) ⟩
      af <*> fmap k ax ∎


open Applicative {{...}} public

{-# DISPLAY Applicative._<*>_ a b = a <*> b #-}
