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

-- boring {{{

Predicate : (A : Set) → Set₁
Predicate A = A → Set

_∨_ : {A : Set} → Predicate A → Predicate A → Predicate A
(P ∨ Q) a = P a ⊎ Q a

_∧_ : {A : Set} → Predicate A → Predicate A → Predicate A
(P ∧ Q) a = P a × Q a

Res : {A B : Set} → (A → B) → (P : Predicate A) → (Σ A P → B)
Res {A} {B} f P = f ∘ proj₁

return : {X C : Set} →
          X → ((X → C) → C)
return = _|>_

_>>=_ : {X Y C : Set} →
        ((X → C) → C) →
        (X → (Y → C) → C) →
        ((Y → C) → C)
cx >>= f = λ y → cx (flip f y)

fmap : {X Y C : Set} →
        (X → Y) →
        ((X → C) → C) →
        ((Y → C) → C)
fmap f c = λ yc → c (yc ∘ f)

unitc : {X C : Set} → X → ((X → C) → C)
unitc x = λ xc → xc x

-- }}}

record Lift {C A : Set} (P : Predicate A) (cont : (A → C) → C) : Set where
  field
    witness : ((Σ A P → C) → C)
    corresponds : cont ≡ λ ac → witness (ac ∘ proj₁)

open Lift

postulate
  C : Set
  A : Set

  c : C

  cont : (A → C) → C

-- Lift P cont implies (∀ f f' : A → C for which Res f P ≡ Res f' P, we have cont f ≡ cont f')

lemmaRes : {P : Predicate A} → Lift P cont → (f f' : A → C) → Res f P ≡ Res f' P → cont f ≡ cont f'
lemmaRes lp f f' eq =
  begin
    cont f
  ≡⟨ cong (_|>_ f) (corresponds lp) ⟩
    witness lp (f ∘ proj₁)
  ≡⟨ cong (witness lp) eq ⟩
    witness lp (f' ∘ proj₁)
  ≡⟨ sym $ cong (_|>_ f') (corresponds lp) ⟩
    cont f' ∎

ext : {P : Predicate A} → (P? : Decidable P) → (Σ A P → C) → (A → C)
ext P? f a with P? a
ext P? f a | yes p = f (a , p)
ext P? f a | no ¬p = c

bla : {P : Predicate A} (P? : Decidable P) → (f : A → C) → (ap : Σ A P) → Res f P ap ≡ Res (ext P? (f ∘ proj₁)) P ap
bla P? f (a , p) with P? a
bla P? f (a , p) | yes p₁ = refl
bla P? f (a , p) | no ¬p with ¬p p
bla P? f (a , p) | no ¬p | ()

extlemma : {P : Predicate A} (P? : Decidable P) → (f : A → C) → Res f P ≡ Res (ext P? (f ∘ proj₁)) P
extlemma {P} P? f = funext (bla P? f)

-- particular case for lemmaREs

lemmaResParticular : {P : Predicate A} → (P? : Decidable P) → Lift P cont → (f : A → C) → cont f ≡ cont (ext P? (f ∘ proj₁))
lemmaResParticular P? lp f = lemmaRes lp f (ext P? (f ∘ proj₁)) (extlemma P? f)

-- reverse {{{

lemmaResPartReverseS : {R : Predicate A} → (R? : Decidable R) →
                   ((f : A → C) → cont f ≡ cont (ext R? (f ∘ proj₁))) →
                   Lift R cont
witness (lemmaResPartReverseS R? x) = cont ∘ ext R?
corresponds (lemmaResPartReverseS P? imp) = funext imp

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
        cont (ext P? (f ∘ proj₁))
      ≡⟨ lemmaResParticular Q? lpQ _ ⟩
        cont (ext Q? ((ext P? (f ∘ proj₁)) ∘ proj₁))
      ≡⟨ cong cont llll ⟩
        cont (ext (P? ∧? Q?) (f ∘ proj₁)) ∎
          where
            llll : (ext Q? ((ext P? (f ∘ proj₁)) ∘ proj₁)) ≡ (ext (P? ∧? Q?) (f ∘ proj₁))
            llll = funext lll
              where
              lll : (a : A) → (ext Q? ((ext P? (f ∘ proj₁)) ∘ proj₁)) a ≡ (ext (P? ∧? Q?) (f ∘ proj₁)) a
              lll a with P? a | Q? a
              lll a | yes p | yes p₁ = sym $ bla P? f (a , p)
              lll a | yes p | no ¬p = refl
              lll a | no ¬p | yes p with P? a
              lll a | no ¬p | yes p | yes p₁ with ¬p p₁
              lll a | no ¬p | yes p | yes p₁ | ()
              lll a | no ¬p | yes p | no ¬p₁ = refl
              lll a | no ¬p | no ¬p₁ = refl
