{-# OPTIONS --allow-unsolved-metas #-}

module LiftProp where

open import Monad
-- open import Imports hiding (_∧_)

open import Postulates

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

-- }}}

Predicate : (A : Set) → Set₁
Predicate A = A → Set

record LiftProp {A : Set} {M : Set → Set} {{ Mimp : Monad M }} (P : Predicate A) (monadicValue : M A) : Set where
  constructor ⟦_<>_⟧
  field
    monadicValueX : M (Σ[ x ∈ A ] P x)
    proofPPE : monadicValue ≡ fmap proj₁ monadicValueX

open LiftProp public

-- Trivial property {{{

implicationLiftProp : ∀{A M} → {{ Mimp : Monad M }} → {P P' : A → Set} → {ma : M A} → ({a : A} → P a → P' a) → LiftProp P ma → LiftProp P' ma
monadicValueX (implicationLiftProp PimpP' prop) = fmap (Data.Product.map₂ PimpP') (monadicValueX prop)
proofPPE (implicationLiftProp PimpP' ⟦ m <> refl ⟧) = law-composition (Data.Product.map₂ PimpP') proj₁ m

-- differentBind {{{

returnLP : {M : Set → Set} → {{ Mimp : Monad M }} →
           {A : Set} → {P : A → Set} →
           (aX : Σ[ a ∈ A ] (P a)) → LiftProp {A} {M} {{Mimp}}  P (return (proj₁ aX))
monadicValueX (returnLP aX) = return aX
proofPPE (returnLP aX) = sym (leftId _ _)

_>>=LP_ : {M : Set → Set} → {{ Mimp : Monad M }} →
         {A B : Set} → {P : A → Set} → {Q : B → Set} →
         {ma : M A} → {f : A → M B} →
            (P[ma] : LiftProp P ma) →
            (flp : (aX : Σ[ a ∈ A ] P a) → LiftProp Q (f (proj₁ aX))) →
              LiftProp Q (ma >>= f)
monadicValueX (⟦ maX <> maXPPE ⟧ >>=LP flp) = maX >>= (monadicValueX ∘ flp)
proofPPE (_>>=LP_ {M} {{Mimp}} {A} {B} {P} {Q} {ma} {f} ⟦ maX <> maXPPE ⟧ flp) =
                   begin
                     ma >>= f
                   ≡⟨ cong (flip _>>=_ f) maXPPE ⟩
                     (do x <- fmap proj₁ maX
                         f x)
                   ≡⟨ fmap->>= f proj₁ maX ⟩
                     (do x ← maX
                         f (proj₁ x))
                   ≡⟨ cong (_>>=_ maX) (funext (proofPPE ∘ flp)) ⟩
                     (do y ← maX
                         fmap proj₁ (monadicValueX (flp y)))
                   ≡⟨ sym $ assoc _ _ _ ⟩
                     fmap proj₁ (do y ← maX
                                    monadicValueX (flp y)) ∎


_>>LP_ : {M : Set → Set} → {{ Mimp : Monad M }} →
         {A B : Set} → {P : A → Set} → {Q : B → Set} →
         {ma : M A} → {mb : M B} →
              (P[ma] : LiftProp P ma) → (Q[mb] : LiftProp Q mb) → LiftProp Q (ma >> mb)
_>>LP_ P[ma] Q[mb] = P[ma] >>=LP λ _ → Q[mb]


-- }}}


-- lift monadic value over ⊤ {{{

toLP : {M : Set → Set} → {{ Mimp : Monad M }} → {A : Set} →
  (ma : M A) → LiftProp (λ _ → ⊤) ma
toLP ma = ⟦ fmap (\x → (x , tt)) ma <> pf ⟧
  where pf : ma ≡ fmap proj₁ (fmap (λ x → x , tt) ma)
        pf = begin
               ma
             ≡⟨ sym $ rightId ma ⟩
               fmap (λ x → x) ma
             ≡⟨ law-composition (λ x → x , tt) proj₁ ma ⟩
               fmap proj₁ (fmap (λ x → x , tt) ma)
             ∎

-- }}}
-- lemma about P ∧ Q {{{

_∧_ : {A : Set} → Predicate A → Predicate A → Predicate A
(P ∧ Q) a = P a × Q a

_∧LP_ : ∀{M A} → {{ Mimp : Monad M }} → {ma : M A} → {P Q : Predicate A} →
  LiftProp P ma → LiftProp Q ma → LiftProp (P ∧ Q) ma
_∧LP_ {M} {A} ⦃ Mimp ⦄ {ma} {P} {Q} maP maQ = {!!}

-- }}}
