module Playground where

open import Functors.IO
open import Applicatives.IO
open import Monads.IO

open import Functors.List
open import Applicatives.List
open import Monads.List

open import Data.Nat
open import Data.Nat.Properties

module Stuff where
  open import FunctorTC
  open import MonadTC
  open import ApplicativeTC

  postulate
    die : IO ℕ

  twoDice : IO ℕ
  twoDice = ⦇ die + die ⦈

  threeDice : IO ℕ
  threeDice = ⦇ ⦇ die + die ⦈ + die ⦈

  thing : {!!}
  thing = {!!}

module Proofs where
  open Stuff
  open import MonadLift renaming (_>>=L_ to _>>=_; returnL to return)
  open import ApplicativeLift renaming (_<*>L_ to _<*>_ ; pureL to pure)
  open import FunctorLift

  bound[_⌜+⌝_] : {x : ℕ} → (n : ℕ) → (m : ℕ) → x ≤ n → {y : ℕ} → y ≤ m → x + y ≤ (n + m)
  bound[ n ⌜+⌝ m ] px py = +-mono-≤ px py

  postulate
    dieBound6 : Lift (λ a → a ≤ 6) die

  twoDiceBound12 : Lift (λ a → a ≤ 12) twoDice
  twoDiceBound12 = ⦇ bound[ 6 ⌜+⌝ 6 ] dieBound6 dieBound6 ⦈

  threeDiceBound18 : Lift (λ a → a ≤ 18) threeDice
  threeDiceBound18 = {!!}

  proof : {!!}
  proof = {!!}

