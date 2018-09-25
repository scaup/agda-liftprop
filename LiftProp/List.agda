{-# OPTIONS --allow-unsolved-metas #-}

module LiftProp.List where

-- Imports {{{
open import LiftProp
open import Monad.List
open import Data.List hiding (filter)

open import Data.Product

open import Relation.Unary using (Decidable)

open import Function public
-- open import Imports hiding (_∧_)
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning
open import Data.Empty
open import Data.Product hiding (map ; zip)
open import Data.Bool hiding (_≟_ ; _∧_; decSetoid)
open import Data.Unit hiding (_≟_ ; decSetoid ; preorder ; setoid ; _≤_ ; _≤?_)
open import Data.Nat
open import Data.Maybe hiding (decSetoid ; setoid ; map)
open import Relation.Nullary


open import Relation.Unary using (Decidable)
-- }}}

filterLP : {A : Set} → {P : A → Set} →
  (P? : Decidable P) → (as : List A) → LiftProp P (Data.List.filter P? as)
filterLP {A} {P} P? as = [ filterX as <> proof as ]
  where
    filterX : (as : List A) → List (Σ[ a ∈ A ] (P a))
    filterX [] = []
    filterX (a ∷ as) with P? a
    filterX (a ∷ as) | yes p = ((a , p)) ∷ filterX as
    filterX (a ∷ as) | no ¬p = filterX as

    proof : (as : List A) → Data.List.filter P? as ≡ fmap proj₁ (filterX as)
    proof [] = refl
    proof (a ∷ as) with P? a
    proof (a ∷ as) | yes p = cong (_∷_ a) (proof as)
    proof (a ∷ as) | no ¬p = proof as


_++LP_ : ∀{A P} → {xs ys : List A} → LiftProp P xs → LiftProp P ys → LiftProp P (xs ++ ys)
[ xsX <> proof₁ ] ++LP [ ysX <> proof₂ ] = [ (xsX ++ ysX) <> {!!} ]

range : ℕ → List ℕ
range zero = []
range (suc n) = range n ++ (n ∷ [])


rangeLP : (n : ℕ) → LiftProp (λ x → x < n) (range n)
rangeLP n = [ f n (n , {!!}) <> {!!} ]
  where
    f : (n : ℕ) → (m : Σ[ x ∈ ℕ ] x ≤ n) → List (Σ[ x ∈ ℕ ] x < n)
    f n (zero , snd) = []
    f n (suc m , snd) = f n (m , {!!})  ++ (m , {!!}) ∷ []


_∧_ : {A : Set} → (P : A → Set) → (Q : A → Set) → (A → Set)
(P ∧ Q) a = P a × Q a

filter : {A : Set} → {P : A → Set} → {Q : A → Set} → {as : List A}
  (Q? : Decidable Q) → LiftProp P as → LiftProp (P ∧ Q) (Data.List.filter Q? as)
filter {A} {P} {Q} {as} Q? asLP = [ {!!} <> {!!} ]
{-
  where
    filterX : (as : List A) → List (Σ[ a ∈ A ] (P a))
    filterX [] = []
    filterX (a ∷ as) with P? a
    filterX (a ∷ as) | yes p = ((a , p)) ∷ filterX as
    filterX (a ∷ as) | no ¬p = filterX as

    proof : (as : List A) → filter P? as ≡ fmap proj₁ (filterX as)
    proof [] = refl
    proof (a ∷ as) with P? a
    proof (a ∷ as) | yes p = cong (_∷_ a) (proof as)
    proof (a ∷ as) | no ¬p = proof as
-}
