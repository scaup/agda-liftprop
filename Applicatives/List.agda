module Applicatives.List where

open import ApplicativeTC

open import FunctorTC
open import Functors.List

open import Data.List
open import Data.List.Properties

open import Function
open import Data.List.Properties
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning

instance
  listApplicative : Applicative List
  Applicative.functorM listApplicative = listFunctor
  Applicative.pure listApplicative x = [ x ]
  (listApplicative Applicative.<*> []) xs = []
  (listApplicative Applicative.<*> (f ∷ fs)) xs = fmap f xs ++ (fs <*> xs)
  Applicative.homomorphism listApplicative = λ f x → refl
  Applicative.interchange listApplicative [] x = refl
  Applicative.interchange listApplicative (f ∷ fs) x = cong (_∷_ (f x)) (interchange fs x)
  Applicative.compositionA listApplicative gs fs xs = {!!}
    where
    compositionList : {X Y Z : Set} → (gs : List (Y → Z)) → (fs : List (X → Y)) → (xs : List X) →
                       (gs <*> (fs <*> xs)) ≡ (((fmap (λ f g → f ∘ g) gs) <*> fs) <*> xs)
    compositionList [] fs xs = refl
    compositionList (g ∷ gs) fs xs =
      begin
        fmap g (fs <*> xs) ++ gs <*> (fs <*> xs)
      ≡⟨ cong (_++_ _) (compositionList gs fs xs) ⟩
        fmap g (fs <*> xs) ++ ((fmap (λ f g → f ∘ g) gs <*> fs) <*> xs)
      ≡⟨ cong (flip _++_ _) (lemma2 g fs xs) ⟩
        (fmap (_∘_ g) fs <*> xs) ++ ((fmap (λ k l → k ∘ l) gs <*> fs) <*> xs)
      ≡⟨ sym $ lemma (fmap (_∘_ g) fs) _ xs ⟩
        (fmap (_∘_ g) fs ++ (fmap (λ k l → k ∘ l) gs <*> fs)) <*> xs
      ≡⟨ {!!} ⟩
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
          ≡⟨ {!!} ⟩
            fmap g (fmap f xs) ++ fmap g (fs <*> xs)
          ≡⟨ {!!} ⟩
            fmap (g ∘ f) xs ++ fmap g (fs <*> xs)
          ≡⟨ {!!} ⟩
            fmap (g ∘ f) xs ++ (fmap (_∘_ g) fs <*> xs) ∎
  Applicative.compatiblefmapA listApplicative = sym (++-identityʳ _)

