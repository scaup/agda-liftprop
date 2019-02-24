{-# OPTIONS --allow-unsolved-metas #-}

module Monads.List where

open import ApplicativeTC
open import FunctorTC
open import Functors.List
open import Applicatives.List

open import Data.List
open import Data.List.Properties
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning

open import Function

module MonadImp where
  _>>=_ : {X Y : Set} → List X → (X → List Y) → List Y
  [] >>= f = []
  (x ∷ xs) >>= f = f x ++ xs >>= f

  leftId : ∀{X Y} → (f : X → List Y) → (x : X) → pure x >>= f ≡ f x
  leftId f x = ++-identityʳ _

  rightId : ∀{X} → (xs : List X) → xs >>= pure ≡ xs
  rightId [] = refl
  rightId (x ∷ xs) = cong (_∷_ _) (rightId xs)

  assoc : {X Y Z : Set} (g : X → List Y) (f : Y → List Z)
          (mx : List X) →
          ((mx >>= g) >>= f) ≡ (mx >>= (λ x → g x >>= f))
  assoc g f [] = refl
  assoc g f (x ∷ xs) =
    begin
      ((x ∷ xs) >>= g) >>= f
    ≡⟨⟩
      (g x ++ (xs >>= g)) >>= f
    ≡⟨ lemma (g x) _ f ⟩
      (g x >>= f) ++ (xs >>= g) >>= f
    ≡⟨ cong (_++_ (g x >>= f)) (assoc g f xs) ⟩
      (g x >>= f) ++ (xs >>= (λ x' → g x' >>= f))
    ≡⟨⟩
      ((x ∷ xs) >>= (λ x₁ → g x₁ >>= f)) ∎
        where
          lemma : {X Y : Set} → (xs x's : List X) → (f : X → List Y) →
                  (xs ++ x's) >>= f ≡ (xs >>= f) ++ (x's >>= f)
          lemma [] x's f = refl
          lemma (x ∷ xs) x's f =
            begin
              f x ++ ((xs ++ x's) >>= f)
            ≡⟨ cong (_++_ (f x)) (lemma xs x's f) ⟩
              f x ++ (xs >>= f) ++ (x's >>= f)
            ≡⟨ associativity (f x) (xs >>= f) _ ⟩
              (f x ++ (xs >>= f)) ++ (x's >>= f) ∎
                where
                  associativity : {X : Set} → (xs ys zs : List X) →
                                  xs ++ (ys ++ zs) ≡ (xs ++ ys) ++ zs
                  associativity [] ys zs = refl
                  associativity (x ∷ xs) ys zs = cong (_∷_ x) (associativity xs ys zs)

  compatible<*> : ∀{X Y} → (fs : List (X → Y)) → (xs : List X) →
                  fs <*> xs ≡ (fs >>= λ f → xs >>= (pure ∘ f))
  compatible<*> [] xs = refl
  compatible<*> (f ∷ fs) xs = cong₂ (_++_) (lemma xs) (compatible<*> fs xs)
    where
      lemma : {X Y : Set} → {f : X → Y} → (xs : List X) → fmap f xs ≡ xs >>= (pure ∘ f)
      lemma [] = refl
      lemma (x ∷ xs) = cong (_∷_ _) (lemma xs)

open import MonadTC

instance
  listMonad : Monad List
  open Monad
  applicativeM listMonad = listApplicative
  _>>=_ listMonad = MonadImp._>>=_
  leftId listMonad = MonadImp.leftId
  rightId listMonad = MonadImp.rightId
  assoc listMonad = MonadImp.assoc
  compatible<*> listMonad = MonadImp.compatible<*>
