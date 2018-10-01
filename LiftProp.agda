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
implicationLiftProp PimpP' record { monadicValueX = monadicValueX ; proofPPE = refl } = record { monadicValueX = mvX ; proofPPE = pPPE }
  where
    impToSigma : {A : Set} → {P : A → Set} → {P' : A → Set} → (imp : {a : A} → P a → P' a) → Σ[ a ∈ A ] (P a) → Σ[ a ∈ A ] (P' a)
    impToSigma imp (a , p) = (a , imp p)
    mvX = fmap (impToSigma PimpP') monadicValueX
    pPPE = law-composition (impToSigma PimpP') proj₁ monadicValueX

-- }}}

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
monadicValueX (_>>=LP_ {M} {{Mimp}} {A} {B} {P} {Q} {ma} {f} ⟦ maX <> maXPPE ⟧ flp) = maX >>= (monadicValueX ∘ flp)
proofPPE (_>>=LP_ {M} {{Mimp}} {A} {B} {P} {Q} {ma} {f} ⟦ maX <> maXPPE ⟧ flp) = sym $
                   begin
                     (
                     fmap proj₁
                     do
                       (a , pa) ← maX
                       monadicValueX (flp ((a , pa)))
                     )
                   ≡⟨ assoc _ _ _ ⟩
                     (
                     do
                       (a , pa) ← maX
                       fmap proj₁ (monadicValueX (flp (a , pa)))
                     )
                     -- maX >>= (λ aX → (monadicValueX (flp aX) >>= (return ∘ proj₁)))
                   ≡⟨ cong (_>>=_ maX) (funext (λ aX → sym (helpLemma (proofPPE (flp aX))))) ⟩
                     (
                     do
                       (a , pa) ← maX
                       x ← f a
                       return x
                     )
                     -- maX >>= (λ aX → (f (proj₁ aX) >>= return))
                   ≡⟨ cong (_>>=_ maX) (funext λ aX → rightId _) ⟩
                     (
                     do
                       (a , pa) ← maX
                       f a
                     )
                     -- maX >>= (λ aX → f (proj₁ aX))
                   ≡⟨ sym (helpLemma maXPPE) ⟩
                     ma >>= f ∎
  where
    helpLemma : {M : Set → Set} {{Mimp : Monad M}} → {A B X : Set} →
                {ma : M A} → {mb : M B} → {p : B → A} → {f : A → M X} → (eq : ma ≡ fmap p mb) →
                ma >>= f ≡ mb >>= (f ∘ p)
    helpLemma {M} {{Mimp}} {A} {B} {X} {ma} {mb} {p} {f} eq =
                            begin
                               ma >>= f
                            ≡⟨ cong (λ z → z >>= f) (eq) ⟩
                              fmap p mb >>= f
                            ≡⟨ assoc _ _ mb ⟩
                              mb >>= (λ x → (return (p x) >>= f))
                            ≡⟨ cong (_>>=_ mb) (funext λ x → (leftId _ (p x) ))  ⟩
                              mb >>= (λ x → f (p x))
                            ≡⟨⟩
                              mb >>= (f ∘ p) ∎


_>>LP_ : {M : Set → Set} → {{ Mimp : Monad M }} →
         {A B : Set} → {P : A → Set} → {Q : B → Set} →
         {ma : M A} → {mb : M B} →
              (P[ma] : LiftProp P ma) → (Q[mb] : LiftProp Q mb) → LiftProp Q (ma >> mb)
_>>LP_ P[ma] Q[mb] = P[ma] >>=LP λ _ → Q[mb]


-- }}}


-- lift monadic value over ⊤ {{{

toLP : {M : Set → Set} → {{ Mimp : Monad M }} → {A : Set} →
  (ma : M A) → LiftProp (λ _ → ⊤) ma
toLP ma = ⟦ fmap (\x → (x , tt)) ma <> {!!} ⟧

-- }}}

-- restricted binds {{{

Res : {A B : Set} → (A → B) → (P : Predicate A) → (Σ A P → B)
Res {A} {B} f P (a , pP) = f a

_≋_ : {A B : Set} → (f g : A → B) → Set
_≋_ {A} {B} f g = (a : A) → f a ≡ g a

_>>=R_ : ∀{M A B P} → {{Mimp : Monad M}} → {ma : M A} →
  (maLP : LiftProp P ma) →
  (fᵣ : Σ A P → M B) → -- it is "enough" to define this restricted function
  M B ×
      (
      (f : (Σ[ f ∈ (A → M B) ] (Res f P ≋ fᵣ) )) →
      ma >>= proj₁ f ≡ monadicValueX maLP >>= fᵣ -- any function which is the same agrees upon...
      )
_>>=R_ {ma = ma} maLP fᵣ = monadicValueX maLP >>= fᵣ , λ{ (f , p) → sym $
  begin (monadicValueX maLP >>= fᵣ)
    ≡⟨ {!!} ⟩
  {!!}
    ≡⟨ {!!} ⟩
  ma >>= f ∎

  }
-- }}}

-- lemma about P ∧ Q {{{

_∧_ : {A : Set} → Predicate A → Predicate A → Predicate A
(P ∧ Q) a = P a × Q a

_∧LP_ : ∀{M A} → {{ Mimp : Monad M }} → {ma : M A} → {P Q : Predicate A} →
  LiftProp P ma → LiftProp Q ma → LiftProp (P ∧ Q) ma
monadicValueX (_∧LP_ {M} {A} ⦃ Mimp ⦄ {ma} {P} {Q} maP maQ) with (maP >>=R λ{ (x , p) → return x}) | (maQ >>=R λ{ (x , q) → return x})
monadicValueX (_∧LP_ {M} {A} ⦃ Mimp ⦄ {ma} {P} {Q} maP maQ) | (ma' , g ) | f = {!!}
proofPPE (_∧LP_ {M} {A} ⦃ Mimp ⦄ {ma} {P} {Q} maP maQ) = {!!}

{- Argument in words {{{

If LiftProp P ma, then if we were to compute ma >>= f for example, it would be sufficient to define f on Σ A P → M B.

Suppose both LiftProp P ma and LiftProp Q ma, then we should be able to prove that it is sufficient to define f on Σ A (Q ∧ P) → M B.

"is sufficient to define f on ..." can be formalized by >>=R..

Take the special case of f = return

}}} -}

-- }}}
