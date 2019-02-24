module Examples.Dice where

open import Data.List
open import Data.Nat

open import MonadTC
open import Monads.IO
open import Monads.List

postulate
  genericDie : IO ℕ

module WithMonad where
  twoDice : IO ℕ
  twoDice = do
                x ← genericDie
                y ← genericDie
                return (x + y)

  twoTimes : IO ℕ → IO ℕ
  twoTimes die = do
                    x ← die
                    y ← die
                    return (x + y)

  twoTimesList : List ℕ → List ℕ
  twoTimesList dieList = do
                    x ← dieList
                    y ← dieList
                    return (x + y)

mopen import Data.Nat
open import Data.Nat.Properties
open import Data.List

open import Examples.Dice

_⌜+⌝_ : {n m : ℕ} {x : ℕ} → x ≤ n → {y : ℕ} → y ≤ m → x + y ≤ (n + m)
_⌜+⌝_ = λ x x₁ → +-mono-≤ x x₁

-- z≤n ⌜+⌝ y = {!!}
-- s≤s px ⌜+⌝ py = s≤s ((px ⌜+⌝ py))

postulate
  sumBound6IsBound12 : {x : ℕ} → x ≤ 6 → {y : ℕ} → y ≤ 6 → x + y ≤ 12

  genericDieBound6 : Lift (λ x → x ≤ 6) genericDie

_infx_ = sumBound6IsBound12

module DiceProofsWithMonad where
  open Examples.Dice.WithMonad

  twoDiceBound12 : Lift (λ a → a ≤ 12) twoDice
  twoDiceBound12 = do
                    (x , px) ← genericDieBound6
                    (y , py) ← genericDieBound6
                    return (x + y , sumBound6IsBound12 px py)

  dieBound6twoTimesBound12 : (die : IO ℕ) → Lift (λ a → a ≤ 6) die → Lift (λ a → a ≤ 12) (twoTimes die)
  dieBound6twoTimesBound12 die dieBound6 = do
                                          (x , px) ← dieBound6
                                          (y , py) ← dieBound6
                                          return (x + y , sumBound6IsBound12 px py)


  dieBound6twoTimesListBound12 : (dieList : List ℕ) → Lift (λ a → a ≤ 6) dieList → Lift (λ a → a ≤ 12) (twoTimesList dieList)
  dieBound6twoTimesListBound12 dieList dieListBound6 = do
                                          (x , px) ← dieListBound6
                                          (y , py) ← dieListBound6
                                          return (x + y , sumBound6IsBound12 px py)


module DiceProofsWithApplicative where
  open Examples.Dice.WithApplicative

  twoDiceBound12 : Lift (λ a → a ≤ 12) twoDice
  twoDiceBound12 = ⦇ genericDieBound6 infx genericDieBound6 ⦈

  dieBound6twoTimesListBound12 : (dieList : IO ℕ) → Lift (λ a → a ≤ 6) dieList →
                                Lift (λ a → a ≤ 12) (twoTimes dieList)
  dieBound6twoTimesListBound12 dieList dieListBound6 =
                  ⦇ sumBound6IsBound12 dieListBound6 dieListBound6 ⦈

  threeTimesBound18 : {die : IO ℕ} → Lift (λ a → a ≤ 6) die → Lift (λ a → a ≤ 18) (threeTimes die)
  threeTimesBound18 dieBound6 = ⦇ (_⌜+⌝_ {12} {6}) ⦇ dieBound6 ⌜+⌝ dieBound6 ⦈ dieBound6 ⦈
odule WithApplicative where
  twoDice : IO ℕ
  twoDice = ⦇ genericDie + genericDie ⦈

  twoTimes : IO ℕ → IO ℕ
  twoTimes die = ⦇ die + die ⦈

  threeTimes : IO ℕ → IO ℕ
  threeTimes die = ⦇ ⦇ die + die ⦈ + die ⦈
