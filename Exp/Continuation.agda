module Exp.Continuation where

open import Postulates

open import Data.Bool hiding (_≟_; _∧_; _∨_)
open import Data.Product
open import Data.Unit
open import Data.Empty
open import Data.Sum

open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Unary using (Decidable)
open import Relation.Nullary
open ≡-Reasoning

open import FunctorTC
open import Functors.Cont
open import FunctorLift

postulate
  C : Set
  A : Set

  c : C

  cont : (A → C) → C

-- Lift P cont implies (∀ f f' : A → C for which Res f P ≡ Res f' P, we have cont f ≡ cont f')

lemmaRes : {P : Predicate A} → Lift P cont → (f f' : A → C) → Res P f ≡ Res P f' → cont f ≡ cont f'
lemmaRes lp f f' eq =
  begin
    cont f
  ≡⟨ cong (_|>_ f) (corresponds lp) ⟩
    witness lp (f ∘ proj₁)
  ≡⟨ cong (witness lp) eq ⟩
    witness lp (f' ∘ proj₁)
  ≡⟨ sym $ cong (_|>_ f') (corresponds lp) ⟩
    cont f' ∎

-- ext extends to values not satisfying P and does not require a proof of P.
-- If P happens to be true, it feeds an arbitrary proof to the original continuation.
-- If P happens to be false, an arbitrary element of C is returned.
ext : {P : Predicate A} → (P? : Decidable P) → (Σ A P → C) → (A → C)
ext P? f a with P? a
ext P? f a | yes p = f (a , p)
ext P? f a | no ¬p = c

extlemma1 : {P : Predicate A} (P? : Decidable P) → (f : A → C) → (ap : Σ A P) → Res P f ap ≡ Res P (ext P? (Res P f)) ap
extlemma1 P? f (a , p) with P? a
extlemma1 P? f (a , p) | yes p₁ = refl
extlemma1 P? f (a , p) | no ¬p with ¬p p
extlemma1 P? f (a , p) | no ¬p | ()

extlemma2 : {P : Predicate A} (P? : Decidable P) → (f : A → C) → Res P f ≡ Res P (ext P? (Res P f))
extlemma2 {P} P? f = funext (extlemma1 P? f)

extlemma3 : {P : Predicate A} (P? : Decidable P) → Res P ≡ Res P ∘ ext P? ∘ Res P
extlemma3 P? = funext (extlemma2 P?)

-- particular case for lemmaREs

lemmaResParticular : {P : Predicate A} → (P? : Decidable P) → Lift P cont → (f : A → C) → cont f ≡ cont (ext P? (Res P f))
lemmaResParticular P? lp f = lemmaRes lp f (ext P? (f ∘ proj₁)) (extlemma2 P? f)

lemmaResParticular2 : {P : Predicate A} → (P? : Decidable P) → Lift P cont → cont ≡ cont ∘ ext P? ∘ Res P
lemmaResParticular2 P? lp = funext (lemmaResParticular P? lp)

-- reverse {{{

lemmaResPartReverseS : {R : Predicate A} → (R? : Decidable R) →
                   ((f : A → C) → cont f ≡ cont (ext R? (Res R f))) →
                   Lift R cont
witness (lemmaResPartReverseS R? x) = cont ∘ ext R?
corresponds (lemmaResPartReverseS P? imp) = funext imp

lemmaResPartReverseS2 : {R : Predicate A} → (R? : Decidable R) →
                   (cont ≡ cont ∘ ext R? ∘ Res R) →
                   Lift R cont
lemmaResPartReverseS2 R? e = lemmaResPartReverseS R? (cong-app e)

-- }}}

_∧?_ : {P Q : Predicate A} → Decidable P → Decidable Q → Decidable (P ∧ Q)
(P? ∧? Q?) a with P? a | Q? a
(P? ∧? Q?) a | yes p | yes q = yes (p , q)
(P? ∧? Q?) a | yes p | no ¬p = no (¬p ∘ proj₂)
(P? ∧? Q?) a | no ¬p | d = no (¬p ∘ proj₁)

_,L_ : {P Q : Predicate A} → {P? : Decidable P} → {Q? : Decidable Q} → Lift P cont → Lift Q cont → Lift (P ∧ Q) cont
_,L_ {P} {Q} {P?} {Q?} lpP lpQ = lemmaResPartReverseS (P? ∧? Q?) easy
  where
    easy : (f : A → C) → cont f ≡ cont (ext (P? ∧? Q?) (f ∘ proj₁))
    easy f =
      begin
        cont f
      ≡⟨ lemmaResParticular P? lpP _  ⟩
        cont ((ext P? ∘ Res P) f)
      ≡⟨ lemmaResParticular Q? lpQ _ ⟩
        cont ((ext Q? ∘ Res Q ∘ ext P? ∘ Res P) f)
      ≡⟨ cong cont llll ⟩
        cont ((ext (P? ∧? Q?) ∘ Res (P ∧ Q)) f) ∎
          where
            llll : (ext Q? ∘ Res Q ∘ ext P? ∘ Res P) f ≡ (ext (P? ∧? Q?) ∘ Res (P ∧ Q)) f
            llll = funext lll
              where
              lll : (a : A) → (ext Q? ∘ Res Q ∘ ext P? ∘ Res P) f a ≡ (ext (P? ∧? Q?) ∘ Res (P ∧ Q)) f a
              lll a with P? a | Q? a
              lll a | yes p | yes p₁ = sym $ extlemma1 P? f (a , p)
              lll a | yes p | no ¬p = refl
              lll a | no ¬p | yes p with P? a
              lll a | no ¬p | yes p | yes p₁ with ¬p p₁
              lll a | no ¬p | yes p | yes p₁ | ()
              lll a | no ¬p | yes p | no ¬p₁ = refl
              lll a | no ¬p | no ¬p₁ = refl

--------------------

module OverUnit {C : Set} {P Q : Predicate ⊤} where

  _,cont_ : ((P tt → C) → C) → ((Q tt → C) → C) → (((P ∧ Q) tt → C) → C)
  (pmu ,cont qmu) pq* = result
    where p* : Q tt → (P tt → C)
          p* q = λ p → pq* (p , q)
          q* : Q tt → C
          q* = pmu ∘ p*
          result : C
          result = qmu q*

  _,LU_ : ∀ {mu : (⊤ → C) → C} → Lift P mu → Lift Q mu → Lift (P ∧ Q) mu
  witness (pmu ,LU qmu) upq* = (pu ,cont qu) pq*
    where pu : (P tt → C) → C
          pu p* = witness pmu (p* ∘ proj₂)
          qu : (Q tt → C) → C
          qu q* = witness qmu (q* ∘ proj₂)
          pq* : (P ∧ Q) tt → C
          pq* (p , q) = upq* (tt , (p , q))
  corresponds (_,LU_ {mu} pmu qmu) = funext λ u* → begin
    mu u*
      ≡⟨ cong-app qmu-cor u* ⟩
    witness qmu ((λ {uq} → u*) ∘ proj₁)
      ≡⟨ cong (witness qmu) (funext (λ {(tt , q) → {!OOPS!!}})) ⟩
    witness qmu (λ uq* → mu u*)
      ≡⟨ cong (λ r → witness qmu (λ uq* → r)) (cong-app pmu-cor u*) ⟩
    witness (pmu ,LU qmu) ((λ {upq} → u*) ∘ proj₁) ∎
    where pmu-cor : mu ≡ λ u* → witness pmu ((λ {up} → u*) ∘ proj₁)
          pmu-cor = corresponds pmu
          qmu-cor : mu ≡ λ u* → witness qmu ((λ {uq} → u*) ∘ proj₁)
          qmu-cor = corresponds qmu
