module Examples.DiceProofs where

open import MonadLift renaming (_>>=L_ to _>>=_; returnL to return)
open import ApplicativeLift renaming (_<*>L_ to _<*>_ ; pureL to pure)
open import FunctorLift

open import Monads.IO
open import Applicatives.IO
open import Functors.IO
open import Monads.List
open import Functors.List

open import Data.Nat
open import Data.Nat.Properties
open import Data.List

open import Examples.Dice

postulate
  sumOfBound6IsBound12 : {x : ℕ} → x ≤ 6 → {y : ℕ} → y ≤ 6 → x + y ≤ 12

  dieBound6 : Lift (λ x → x ≤ 6) die

module DiceProofsWithMonad where
  open Examples.Dice.WithMonad

  twoDiceBound12 : Lift (λ a → a ≤ 12) twoDice
  twoDiceBound12 = do
                    (x , px) ← dieBound6
                    (y , py) ← dieBound6
                    return (x + y , sumOfBound6IsBound12 px py)

  dieBound6twoTimesBound12 : (die : IO ℕ) → Lift (λ a → a ≤ 6) die → Lift (λ a → a ≤ 12) (twoTimes die)
  dieBound6twoTimesBound12 die dieBound6 = do
                                          (x , px) ← dieBound6
                                          (y , py) ← dieBound6
                                          return (x + y , sumOfBound6IsBound12 px py)


  dieBound6twoTimesListBound12 : (dieList : List ℕ) → Lift (λ a → a ≤ 6) dieList → Lift (λ a → a ≤ 12) (twoTimesList dieList)
  dieBound6twoTimesListBound12 dieList dieListBound6 = do
                                          (x , px) ← dieListBound6
                                          (y , py) ← dieListBound6
                                          return (x + y , sumOfBound6IsBound12 px py)


module DiceProofsWithApplicative where
  open Examples.Dice.WithApplicative

  twoDiceBound12 : Lift (λ a → a ≤ 12) twoDice
  twoDiceBound12 = ⦇ sumOfBound6IsBound12 dieBound6 dieBound6 ⦈

  dieBound6twoTimesListBound12 : (dieList : IO ℕ) → Lift (λ a → a ≤ 6) dieList →
                                Lift (λ a → a ≤ 12) (twoTimes dieList)
  dieBound6twoTimesListBound12 dieList dieListBound6 =
                  ⦇ sumOfBound6IsBound12 dieListBound6 dieListBound6 ⦈
