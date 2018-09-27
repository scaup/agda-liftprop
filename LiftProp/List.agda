{-# OPTIONS --allow-unsolved-metas #-}

module LiftProp.List where

-- Imports {{{

open import LiftProp
open import Monad.List
open import Data.List
open import Data.Product
open import Data.Nat
open import Relation.Unary using (Decidable)

-- }}}



_++LP_ : ∀{A P} → {xs ys : List A} → LiftProp P xs → LiftProp P ys → LiftProp P (xs ++ ys)
⟦ xsX <> proof₁ ⟧ ++LP ⟦ ysX <> proof₂ ⟧ = ⟦ (xsX ++ ysX) <> {!!} ⟧


rangeLP : (n : ℕ) → LiftProp (λ x → x < n) (range n)
rangeLP n = ⟦ f n (n , {!!}) <> {!!} ⟧
  where
    f : (n : ℕ) → (m : Σ[ x ∈ ℕ ] x ≤ n) → List (Σ[ x ∈ ℕ ] x < n)
    f n (zero , snd) = []
    f n (suc m , snd) = f n (m , {!!})  ++ (m , {!!}) ∷ []



filterLPT : {A : Set} → {P : A → Set} → {Q : A → Set} → {as : List A}
  (Q? : Decidable Q) → LiftProp P as → LiftProp (P ∧ Q) (Data.List.filter Q? as)
filterLPT {A} {P} {Q} {as} Q? asLP = ⟦ {!!} <> {!!} ⟧


filterLP : {A : Set} → {P : A → Set} →
  (P? : Decidable P) → (as : List A) → LiftProp P (filter P? as)
filterLP {A} {P} P? as = implicationLiftProp (λ{ (_ , x) → x}) alpha
  where
    alpha = filterLPT P? (toLP as)
