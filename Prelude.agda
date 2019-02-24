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
