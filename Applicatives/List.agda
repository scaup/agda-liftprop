module Applicatives.List where

open import FunctorTC
open import Functors.List public

open import Data.List
open import Data.List.Properties

open import Function
open import Data.List.Properties
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning

module ApplicativeImp where
  _<*>_ : {X Y : Set} → List (X → Y) → List X → List Y
  [] <*> xs = []
  (f ∷ fs) <*> xs = fmap f xs ++ (fs <*> xs)

  pure : {X : Set} → X → List X
  pure x = [ x ]

  interchange : ∀{X Y} → (fs : List (X → Y)) → (x : X) → fs <*> pure x ≡ fmap (λ k → k x) fs
  interchange [] x = refl
  interchange (f ∷ fs) x = cong (_∷_ (f x)) (interchange fs x)

  compositionA : {X Y Z : Set} → (gs : List (Y → Z)) → (fs : List (X → Y)) → (xs : List X) →
                     (gs <*> (fs <*> xs)) ≡ (((fmap (λ f g → f ∘ g) gs) <*> fs) <*> xs)
  compositionA [] fs xs = refl
  compositionA (g ∷ gs) fs xs =
    begin
      fmap g (fs <*> xs) ++ gs <*> (fs <*> xs)
    ≡⟨ cong (_++_ _) (compositionA gs fs xs) ⟩
      fmap g (fs <*> xs) ++ ((fmap (λ f g → f ∘ g) gs <*> fs) <*> xs)
    ≡⟨ cong (flip _++_ _) (lemma2 g fs xs) ⟩
      (fmap (_∘_ g) fs <*> xs) ++ ((fmap (λ k l → k ∘ l) gs <*> fs) <*> xs)
    ≡⟨ sym $ lemma (fmap (_∘_ g) fs) _ xs ⟩
      (fmap (_∘_ g) fs ++ (fmap (λ k l → k ∘ l) gs <*> fs)) <*> xs ∎
    where
      lemma : {X Y : Set} → (fs fs' : List (X → Y)) → (xs : List X) →
              (fs ++ fs') <*> xs ≡ fs <*> xs ++ fs' <*> xs
      lemma [] fs' xs = refl
      lemma (f ∷ fs) fs' xs =
        begin
          fmap f xs ++ ((fs ++ fs') <*> xs)
        ≡⟨ cong (_++_ _) (lemma fs fs' _) ⟩
          fmap f xs ++ ((fs <*> xs) ++ (fs' <*> xs))
        ≡⟨ sym $ ++-assoc (fmap f xs) _ _  ⟩
          (fmap f xs ++ (fs <*> xs)) ++ (fs' <*> xs) ∎
      lemma2 : {X Y Z : Set} → (g : Y → Z) → (fs : List (X → Y)) → (xs : List X) →
        fmap g (fs <*> xs) ≡ fmap (_∘_ g) fs <*> xs
      lemma2 g [] xs = refl
      lemma2 g (f ∷ fs) xs =
        begin
          fmap g (fmap f xs ++ (fs <*> xs))
        ≡⟨ fmapAssoc (fmap f xs) _ ⟩
          fmap g (fmap f xs) ++ (fmap g (fs <*> xs))
        ≡⟨ cong (flip _++_ _) (sym $ composition f g xs) ⟩
          fmap (g ∘ f) xs ++ fmap g (fs <*> xs)
        ≡⟨ cong (_++_ _) (lemma2 g fs xs) ⟩
          fmap (g ∘ f) xs ++ (fmap (_∘_ g) fs <*> xs) ∎

open import ApplicativeTC

instance
  listApplicative : Applicative List
  listApplicative = record
                      { pure = ApplicativeImp.pure
                      ; _<*>_ = ApplicativeImp._<*>_
                      ; homomorphism = λ f x → refl
                      ; interchange = ApplicativeImp.interchange
                      ; compositionA = ApplicativeImp.compositionA
                      ; compatiblefmapA = sym (++-identityʳ _)
                      }
