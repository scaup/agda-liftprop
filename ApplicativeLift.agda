open import ApplicativeTC

module ApplicativeLift {F : Set → Set} {{app : Applicative F}} where

open import Relation.Binary.PropositionalEquality

open import FunctorLift {F}

private
  pureLExplicit : {X : Set} → {P : Predicate X} →
                  (xp : Σ X P) → Lift P (pure (proj₁ xp))
  witness (pureLExplicit xp) = pure xp
  corresponds (pureLExplicit (x , p)) = sym $ homomorphism _ _

  _<*>LExplicit_ : {X Y : Set} → {P : Predicate X} → {Q : Predicate Y} →
              {af : F (X → Y)} → {ax : F X} →
            Lift (λ f → (xp : Σ X P) → Q (f (proj₁ xp))) af → Lift P ax → Lift Q (af <*> ax)
  witness (lfs <*>LExplicit lp) = fmapR (λ{ (f , pf) → λ{ (x , p) → (f x) , pf (x , p) }}) lfs <*> witness lp
  corresponds (_<*>LExplicit_ {af = af} {ax = ax} lfs lp) = sym $
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

pureL : {X : Set} → {P : X → Set} →
        {x : X} → (p : P x) → Lift P (pure x)
pureL p = pureLExplicit (_ , p)

_<*>L_ : {X Y : Set} → {P : Predicate X} → {Q : Predicate Y} →
          {af : F (X → Y)} → {ax : F X} →
            Lift (P ↦ Q) af → Lift P ax → Lift Q (af <*> ax)
lfs <*>L lp = applyL (λ{ imp (x , p) → imp p}) lfs <*>LExplicit lp

_<*>R_ : ∀{X Y P} → {ax : F X} → F (Σ X P → Y) → Lift P ax → F Y
fR <*>R axP = fR <*> witness axP

-- applyValid : ∀{}
