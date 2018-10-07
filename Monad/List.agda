module Monad.List where

-- stdlib {{{

open import Data.Nat
open import Data.Bool hiding (_≟_; _∧_)
open import Data.Product
open import Data.Unit hiding (_≟_; _≤?_; _≤_)
open import Data.Empty
open import Data.Sum
open import Function

open import Relation.Unary using (Decidable)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Agda.Builtin.IO public
open import Agda.Builtin.String public

open import Data.List

-- }}}

open import Monad

instance
  listMonad : Monad List
  listMonad = record
                { return = returnList ;
                  _>>=_ = _>>=List_ ;
                  leftId = leftIdList ;
                  rightId = rightIdList ;
                  assoc = assocList }
    where
      returnList : {X : Set} → X → List X
      returnList x = x ∷ []

      _>>=List_ : {X Y : Set} → List X → (X → List Y) → List Y
      [] >>=List f = []
      (x ∷ xs) >>=List f = f x ++ (xs >>=List f)

      leftIdList : {X Y : Set} → (f : X → List Y) → (x : X) → f x ++ [] ≡ f x
      leftIdList f x = lemma
        where
          lemma : {X : Set} → {xs : List X} → xs ++ [] ≡ xs
          lemma {X} {[]} = refl
          lemma {X} {x ∷ xs} = cong (_∷_ x) (lemma {X} {xs})

      rightIdList : {X : Set} (m : List X) → (m >>=List returnList) ≡ m
      rightIdList [] = refl
      rightIdList (x ∷ xs) = cong (_∷_ x) (rightIdList xs)

      assocList : {X Y Z : Set} (g : X → List Y) (f : Y → List Z)
              (mx : List X) →
              ((mx >>=List g) >>=List f) ≡ (mx >>=List (λ x → g x >>=List f))
      assocList g f [] = refl
      assocList g f (x ∷ xs) =
        begin
          ((x ∷ xs) >>=List g) >>=List f
        ≡⟨⟩
          (g x ++ (xs >>=List g)) >>=List f
        ≡⟨ lemma (g x) _ f ⟩
          (g x >>=List f) ++ (xs >>=List g) >>=List f
        ≡⟨ cong (_++_ (g x >>=List f)) (assocList g f xs) ⟩
          (g x >>=List f) ++ (xs >>=List (λ x' → g x' >>=List f))
        ≡⟨⟩
          ((x ∷ xs) >>=List (λ x₁ → g x₁ >>=List f)) ∎
            where
              lemma : {X Y : Set} → (xs x's : List X) → (f : X → List Y) →
                      (xs ++ x's) >>=List f ≡ (xs >>=List f) ++ (x's >>=List f)
              lemma [] x's f = refl
              lemma (x ∷ xs) x's f =
                begin
                  f x ++ ((xs ++ x's) >>=List f)
                ≡⟨ cong (_++_ (f x)) (lemma xs x's f) ⟩
                  f x ++ (xs >>=List f) ++ (x's >>=List f)
                ≡⟨ associativity (f x) (xs >>=List f) _ ⟩
                  (f x ++ (xs >>=List f)) ++ (x's >>=List f) ∎
                    where
                      associativity : {X : Set} → (xs ys zs : List X) →
                                      xs ++ (ys ++ zs) ≡ (xs ++ ys) ++ zs
                      associativity [] ys zs = refl
                      associativity (x ∷ xs) ys zs = cong (_∷_ x) (associativity xs ys zs)


range : ℕ → List ℕ
range zero = []
range (suc n) = n ∷ range n
