{-# OPTIONS --allow-unsolved-metas #-}

module LiftProp.List where

-- Imports {{{

open import Function
open import LiftProp
open import Monad.List
open import Monad2Functor
open import Functor
open import Data.List
open import Data.Product
open import Data.Nat
open import Relation.Unary using (Decidable)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

-- }}}

α : {A : Set} → {xs ys : List A} → {x y : A} → x ∷ xs ≡ y ∷ ys → x ≡ y × xs ≡ ys
α refl = refl , refl


_∷LP_ : {A : Set} → {P : Predicate A} → {xs : List A} →
  (ap : Σ A P) → LiftProp P xs → LiftProp P (proj₁ ap ∷ xs)
ap ∷LP ⟦ xsX <> proofPPE₁ ⟧ = ⟦ ap ∷ xsX <> cong (_∷_ (proj₁ ap)) proofPPE₁ ⟧


_++LP_ : ∀{A P} → {xs ys : List A} → LiftProp P xs → LiftProp P ys → LiftProp P (xs ++ ys)
_++LP_ {A} {P} {[]} {ys} ⟦ [] <> proof₁ ⟧ lpys = lpys
_++LP_ {A} {P} {x ∷ xs} {ys} ⟦ [] <> () ⟧ ⟦ ysX <> proof₂ ⟧
_++LP_ {A} {P} {[]} {ys} ⟦ x ∷ xsX <> () ⟧ ⟦ ysX <> proof₂ ⟧
_++LP_ {A} {P} {x₁ ∷ xs} {ys} ⟦ (x , p) ∷ xsX <> proof₁ ⟧ lpys with α proof₁
_++LP_ {A} {P} {x₁ ∷ xs} {ys} ⟦ (.x₁ , p) ∷ xsX <> proof₁ ⟧ lpys | refl , e = (x₁ , p) ∷LP (⟦ xsX <> e ⟧ ++LP lpys)


rangeLP : (n : ℕ) → LiftProp (λ x → x < n) (range n)
rangeLP = {!!}
  where
    f : (n : ℕ) → (m : Σ[ m ∈ ℕ ] m ≤ n) → LiftProp (λ x → x < n) (range (proj₁ m))
    f n (zero , snd) = ⟦ [] <> refl ⟧
    f zero (suc m , ())
    f (suc n) (suc m , s≤s snd) = (m , (s≤s snd)) ∷LP f (suc n) (m , {!g ?!}) --maybe try with _≤'_ ?
      where
        g : {m n : ℕ} → suc m ≤ n → m ≤ n
        g {m} {.(suc _)} (s≤s e) = h e
          where
            h : {x y : ℕ} → x ≤ y → x ≤ suc y
            h z≤n = z≤n
            h (s≤s e) = s≤s (h e)


_∧LPlist_ : {A : Set} → {as : List A} → {P Q : Predicate A} →
  LiftProp P as → LiftProp Q as → LiftProp (P ∧ Q) as
_∧LPlist_ {as = []} lpP lpQ = ⟦ [] <> refl ⟧
_∧LPlist_ {as = x ∷ as} ⟦ [] <> () ⟧ lpQ
_∧LPlist_ {as = x ∷ as} ⟦ x₁ ∷ a <> proofPPE₁ ⟧ ⟦ [] <> () ⟧
_∧LPlist_ {as = x ∷ as} ⟦ x₁ ∷ a <> proofPPE₁ ⟧ ⟦ x₂ ∷ c <> proofPPE₂ ⟧ with α proofPPE₁ | α proofPPE₂
_∧LPlist_ {_} {x ∷ as} ⟦ (.x , px) ∷ xps <> proofPPE₁ ⟧ ⟦ (.x , qx) ∷ xqs <> proofPPE₂ ⟧ | refl , snd | refl , snd₁ = (x , px , qx) ∷LP (⟦ xps <> snd ⟧ ∧LPlist ⟦ xqs <> snd₁ ⟧)



filterNewLP : {A : Set} → {P : A → Set} →
  (P? : Decidable P) → (as : List A) → LiftProp P (filter P? as)
filterNewLP {A} {P} P? [] = ⟦ [] <> refl ⟧
filterNewLP {A} {P} P? (x ∷ as) with P? x
filterNewLP {A} {P} P? (x ∷ as) | yes p = (x , p) ∷LP filterNewLP P? as
filterNewLP {A} {P} P? (x ∷ as) | no ¬p = filterNewLP P? as

filterPreservesLP : {A : Set} → {P : A → Set} → {Q : A → Set} → {as : List A}
  (Q? : Decidable Q) → LiftProp P as → LiftProp P (Data.List.filter Q? as)
filterPreservesLP {A} {P} {Q} {[]} Q? ⟦ monadicValueX₁ <> proofPPE₁ ⟧ = ⟦ monadicValueX₁ <> proofPPE₁ ⟧
filterPreservesLP {A} {P} {Q} {x ∷ as} Q? ⟦ [] <> () ⟧
filterPreservesLP {A} {P} {Q} {x ∷ as} Q? ⟦ (x₁ , p₁) ∷ m <> p ⟧ with Q? x₁ | α p
filterPreservesLP {A} {P} {Q} {x ∷ as} Q? ⟦ (.x , p₁) ∷ m <> p ⟧ | yes p₂ | refl , ppp = congLP θ (((x , p₁)) ∷LP filterPreservesLP Q? ⟦ m <> ppp ⟧)
  where
    θ : x ∷ filter Q? as ≡ (filter Q? (x ∷ as))
    θ with Q? x
    θ | yes p = refl
    θ | no ¬p with ¬p p₂
    θ | no ¬p | ()
filterPreservesLP {A} {P} {Q} {x ∷ as} Q? ⟦ (.x , p₁) ∷ m <> p ⟧ | no ¬p | refl , ppp = congLP θ (filterPreservesLP Q? ⟦ m <> ppp ⟧)
  where
    θ : filter Q? as ≡ filter Q? (x ∷ as)
    θ with Q? x
    θ | yes p' with ¬p p'
    θ | yes p' | ()
    θ | no ¬p' = refl
