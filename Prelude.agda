module Prelude where

open import Data.Sum
open import Data.Product
open import Function

Predicate : (A : Set) → Set₁
Predicate A = A → Set

_∨_ : {A : Set} → Predicate A → Predicate A → Predicate A
(P ∨ Q) a = P a ⊎ Q a

_∧_ : {A : Set} → Predicate A → Predicate A → Predicate A
(P ∧ Q) a = P a × Q a

-- Res restricts to values satisfying P by ignoring the proof of P.
Res : {A B : Set} → (P : Predicate A) → (A → B) → (Σ A P → B)
Res {A} {B} P f = f ∘ proj₁

_↦_ : {X Y : Set} → Predicate X → Predicate Y → Predicate (X → Y)
(_↦_ {X} P Q) f = {x : X} → P x → Q (f x)

module Booleans where
  open import Data.Bool hiding (_≟_) renaming (_∧_ to _&&_; _∨_ to _||_) public

module Integers where
  open import Data.Bool hiding (_≟_) renaming (_∧_ to _&&_; _∨_ to _||_)

  open import Data.List
  open import Data.Nat renaming (_≟_ to _≟ℕ_) public
  open import Data.Integer using (ℤ) renaming (_≟_ to _≟ℤ_ ; _⊖_ to _-_ ; _+_ to _+ℤ_ ; _<_ to _<ℤ_) public

  open import Relation.Binary
  open import Relation.Nullary
  open import Relation.Binary.PropositionalEquality hiding ([_])

  record EqDec (A : Set) : Set where
    field
      _≟_ : Decidable {A = A} _≡_

    _==_ : A → A → Bool
    a₁ == a₂ with a₁ ≟ a₂
    (a₁ == a₂) | yes p = true
    (a₁ == a₂) | no ¬p = false

    to≡ : {x y : A} → x == y ≡ true → x ≡ y
    to≡ {x} {y} b with x ≟ y
    to≡ {x} {y} b | yes p = p
    to≡ {x} {y} () | no ¬p

    to≢ : {x y : A} → x == y ≡ false → x ≢ y
    to≢ {x} {y} b with x ≟ y
    to≢ {x} {y} () | yes p
    to≢ {x} {y} refl | no ¬p = ¬p

    _∈_ : A → List A → Bool
    _∈_ a [] = false
    _∈_ a (x ∷ as) = x == a || _∈_ a as

    _∉_ : A → List A → Bool
    _∉_ a as = not $ a ∈ as

  open EqDec {{...}} public

  instance
    eqDecℤ : EqDec ℤ
    eqDecℤ = record { _≟_ = _≟ℤ_ }

  instance
    eqDecℕ : EqDec ℕ
    eqDecℕ = record { _≟_ = _≟ℕ_ }
