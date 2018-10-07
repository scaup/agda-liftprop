module Password where

open import LiftProp
open import Monad
open import Monad.IO

-- stdlib {{{

open import Data.Nat
open import Data.List
open import Data.Bool hiding (_≟_; _∧_)
open import Data.Product
open import Data.Unit hiding (_≟_; _≤?_; _≤_)
open import Data.Empty
open import Data.Sum
open import Function

open import Relation.Unary using (Decidable)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

-- }}}

postulate
  entropy : String → ℕ

-- if then stuff {{{

if?_then_else_ : {A P : Set} → Dec P → A → A → A
if? yes p then a else b = a
if? no ¬p then a else b = b

if?_then_elseX_ : {A P : Set} → Dec P → A → (¬ P → A) → A
if? yes p then a elseX b = a
if? no ¬p then a elseX f = f ¬p

if?_thenX_else_ : {A P : Set} → Dec P → (P → A) → A → A
if? yes p thenX f else b = f p
if? no ¬p thenX f else b = b

if?_thenX_elseX_ : {A P : Set} → (d : Dec P) → (P → A) → (¬ P → A) → A
if? yes p thenX f elseX g = f p
if? no ¬p thenX f elseX g = g ¬p

-- }}}

-- ifLP then stuff {{{

if?LP_thenX_elseX_ : ∀{M A} → {{Mimp : Monad M}} →
  {Q : Predicate A} → {ma₁ ma₂ : M A} →
  {P : Set} → (d : Dec P) →
  (P → LiftProp Q ma₁) → (¬ P → LiftProp Q ma₂) →
  LiftProp Q (if? d then ma₁ else ma₂)
if?LP yes p thenX f elseX g = f p
if?LP no ¬p thenX f elseX g = g ¬p

-- }}}

{-# TERMINATING #-}
choosePassword : IO String
choosePassword = do
                   s ← getLine
                   if? 42 ≤? entropy s
                     then return s
                     else choosePassword


{-# NON_TERMINATING #-}
chosenPasswordsStrongEnough : LiftProp (λ s → (42 ≤ entropy s)) choosePassword
chosenPasswordsStrongEnough =
  let
    _>>=_ = _>>=LP_
    return = returnLP
    b = true
  in
  do
    (s , _) ← toLP getLine
    if?LP 42 ≤? entropy s
      thenX (λ p → return (s , p))
      elseX (λ _ → chosenPasswordsStrongEnough)
