module MonadTC where

open import ApplicativeTC public
open import Postulates

open import Function
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

return = pure

record Monad (M : Set → Set) : Set₁ where
  field
    {{applicativeM}} : Applicative M
    _>>=_ : {X Y : Set} → (M X) → (X → M Y) → (M Y)
    leftId : {X Y : Set} → (f : X → M Y) → (x : X) →
             pure x >>= f ≡ f x
    rightId : {X : Set} → (m : M X) →
              m >>= pure ≡ m
    assoc : {X Y Z : Set} → (g : X → M Y) → (f : Y → M Z) → (mx : M X) →
            (mx >>= g) >>= f ≡ mx >>= (λ x → g x >>= f)
    compatible<*> : ∀{X Y} → (mf : M (X → Y)) → (mx : M X) →
                    mf <*> mx ≡ (mf >>= λ f → mx >>= (pure ∘ f))

  _>>_ : {X Y : Set} → M X → M Y → M Y
  mx >> my = mx >>= λ _ → my


  compatiblefmap : {X Y : Set} → {f : X → Y} → {mx : M X} →
                   fmap f mx ≡ mx >>= (return ∘ f)
  compatiblefmap {X} {Y} {f} {mx} = sym $
    begin
      mx >>= (return ∘ f)
    ≡⟨ sym (leftId _ _) ⟩
       return f >>= (λ f → (mx >>= (return ∘ f)))
    ≡⟨ sym $ compatible<*> _ _ ⟩
      pure f <*> mx
    ≡⟨ sym compatiblefmapA ⟩
      fmap f mx ∎

  fmap->>= : {A B C : Set} →
    (g : B → M C) → (f : A → B) → (mx : M A) → (fmap f mx) >>= g ≡ mx >>= (g ∘ f)
  fmap->>= g f mx = begin
                      fmap f mx >>= g
                    ≡⟨ cong (flip _>>=_ g) compatiblefmap ⟩
                      (mx >>= (return ∘ f)) >>= g
                    ≡⟨ assoc _ _ _ ⟩
                      mx >>= (λ x → return (f x) >>= g)
                    ≡⟨ cong (_>>=_ mx) (funext (leftId g ∘ f)) ⟩
                      mx >>= (g ∘ f)
                    ∎

  fmap-return : {A B : Set} → (f : A → B) → (a : A) → fmap f (return a) ≡ return (f a)
  fmap-return f a =
    begin
      fmap f (return a)
    ≡⟨ compatiblefmap ⟩
      return a >>= (λ x → return (f x))
    ≡⟨ leftId _ _ ⟩
      return (f a) ∎

  fmap-move->>= : {A B C : Set} →
    (f : A → M B) → (ma : M A) → (g : B → C) →
    (fmap g (ma >>= f)) ≡ (ma >>= (fmap g ∘ f))
  fmap-move->>= f ma g =
    begin
      fmap g (ma >>= f)
    ≡⟨ compatiblefmap ⟩
      (ma >>= f) >>= (return ∘ g)
    ≡⟨ assoc _ _ _ ⟩
      (ma >>= (λ a → f a >>= (return ∘ g)))
    ≡⟨ cong (_>>=_ ma) (funext (λ _ → sym compatiblefmap)) ⟩
      (ma >>= (fmap g ∘ f)) ∎

open Monad {{...}} public

{-# DISPLAY Monad._>>=_ imp a b = a >>= b #-}
-- {-# DISPLAY Monad.return i a = return a #-}
-- {-# DISPLAY Monad.return i = return #-} -- f ∘ return
