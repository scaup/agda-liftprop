{-# OPTIONS --allow-unsolved-metas #-}

module Lift.ApplicativeTC where

open import Lift
open import ApplicativeTC

open import Postulates

-- stdlib {{{

open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- }}}

pureLold : {A : Set → Set} → {{ _ : Applicative A }} →
           {X : Set} → {P : X → Set} →
           (xp : Σ X P) → Lift {X} {A} P (pure (proj₁ xp))
witness (pureLold xp) = pure xp
corresponds (pureLold (x , p)) = sym $
  begin
    fmap proj₁ (pure (x , p))
  ≡⟨ compatiblefmapA ⟩
    pure proj₁ <*> (pure (x , p))
  ≡⟨ homomorphism proj₁ (x , p) ⟩
    pure x ∎

pureL : {A : Set → Set} → {{ _ : Applicative A }} →
           {X : Set} → {P : X → Set} →
           {x : X} → (p : P x) → Lift {X} {A} P (pure x)
pureL p = pureLold (_ , p)


move : {A : Set → Set} → {{ _ : Applicative A }} →
       {X Y Z : Set} →
       (k : Y → Z) → (af : A (X → Y)) → (ax : A X) →
       fmap k (af <*> ax) ≡ fmap (λ x2y → k ∘ x2y) af <*> ax
move k af ax =
  begin
    fmap k (af <*> ax)
  ≡⟨ compatiblefmapA ⟩
    pure k <*> (af <*> ax)
  ≡⟨ compositionA _ af ax ⟩
    ((pure (λ f g → f ∘ g) <*> pure k) <*> af) <*> ax
  ≡⟨ cong (flip _<*>_ _) (cong (flip _<*>_ _) (homomorphism _ _)) ⟩
    (pure ((λ f g → f ∘ g) k) <*> af) <*> ax
  ≡⟨ refl ⟩
    (pure ((λ f → k ∘ f)) <*> af) <*> ax
  ≡⟨ cong (flip _<*>_ _) (sym compatiblefmapA ) ⟩
    fmap (λ x2y → k ∘ x2y) af <*> ax ∎

move' : {A : Set → Set} → {{ _ : Applicative A }} →
       {X Y Z : Set} →
       (k : X → Y) → (af : A (Y → Z)) → (ax : A X) →
       fmap (λ f → f ∘ k) af <*> ax ≡ af <*> fmap k ax
move' k af ax =
  begin
    fmap (λ f → f ∘ k) af <*> ax
  ≡⟨ refl ⟩
    fmap ((λ z → z k) ∘ (λ f g x → f (g x))) af <*> ax
  ≡⟨ cong (flip _<*>_ _) (composition (λ f g x → f (g x)) (λ z → z k) af) ⟩
    fmap (λ z → z k) (fmap (λ f g → f ∘ g) af) <*> ax
  ≡⟨ cong (λ a → a <*> _) compatiblefmapA ⟩
    (pure (λ z → z k) <*> (fmap (λ f g → f ∘ g) af)) <*> ax
  ≡⟨ cong (λ a → (_ <*> a) <*> _) compatiblefmapA ⟩
    (pure (λ z → z k) <*> (pure (λ f g → f ∘ g) <*> af)) <*> ax
  ≡⟨ cong (flip _<*>_ _) (sym $ interchange _ _) ⟩
    ((pure (λ f g → f ∘ g) <*> af) <*> pure k) <*> ax
  ≡⟨ sym (compositionA _ _ _) ⟩
    af <*> (pure k <*> ax)
  ≡⟨ cong (_<*>_ _) (sym compatiblefmapA) ⟩
    af <*> fmap k ax ∎

_<*>Lold_ : {A : Set → Set} → {{ _ : Applicative A }} →
         {X Y : Set} → {P : Predicate X} → {Q : Predicate Y} →
         {af : A (X → Y)} → {ax : A X} →
           Lift (λ f → (xp : Σ X P) → Q (f (proj₁ xp))) af → Lift P ax → Lift Q (af <*> ax)
witness (lfs <*>Lold lp) = fmapR (λ{ (f , pf) → λ{ (x , p) → (f x) , pf (x , p) }}) lfs <*> witness lp
corresponds (_<*>Lold_ {af = af} {ax = ax} lfs lp) = sym $
  begin
    fmap proj₁ (fmap (λ{ (f , pf) → λ{ (x , p) → (f x) , pf (x , p) }}) (witness lfs) <*> witness lp)
  ≡⟨ move _ _ _ ⟩
    fmap (λ z → proj₁ ∘ z) (fmap (λ{ (f , pf) → λ{ (x , p) → (f x) , pf (x , p) }}) (witness lfs)) <*> witness lp
  ≡⟨ cong (flip _<*>_ _) (sym (composition _ _ _)) ⟩
    fmap ((λ{ (f , pf) → λ{ (x , p) → (f x) }})) (witness lfs) <*> witness lp
  ≡⟨ refl ⟩
    fmapR ((λ{ (f , pf) → λ{ (x , p) → (f x) }})) lfs <*> witness lp
  ≡⟨ cong (flip _<*>_ _) (fmapRValid _ lfs _ _ refl) ⟩
    fmap ((λ f → λ{ (x , p) → (f x) })) af <*> witness lp
  ≡⟨ refl ⟩
    fmap (λ f → f ∘ proj₁) af <*> witness lp
  ≡⟨ move' _ _ _  ⟩
    af <*> fmap proj₁ (witness lp)
  ≡⟨ cong (_<*>_ _) (sym $ corresponds lp) ⟩
    (af <*> ax) ∎

_↦_ : {X Y : Set} → Predicate X → Predicate Y → Predicate (X → Y)
(_↦_ {X} P Q) f = {x : X} → P x → Q (f x)

_<*>L_ : {A : Set → Set} → {{ _ : Applicative A }} →
          {X Y : Set} → {P : Predicate X} → {Q : Predicate Y} →
          {af : A (X → Y)} → {ax : A X} →
            Lift (P ↦ Q) af → Lift P ax → Lift Q (af <*> ax)
lfs <*>L lp = applyL (λ{ imp (x , p) → imp p}) lfs <*>Lold lp
