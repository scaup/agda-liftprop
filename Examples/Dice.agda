module Examples.Dice where

open import Data.List
open import Data.Nat

open import MonadTC
open import ApplicativeTC
open import Monads.IO
open import Applicatives.IO
open import Monads.List
open import Applicatives.List

postulate
  die : IO ℕ

module WithMonad where
  twoDice : IO ℕ
  twoDice = do
                x ← die
                y ← die
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

module WithApplicative where

  twoDice : IO ℕ
  twoDice = ⦇ die + die ⦈

  twoTimes : IO ℕ → IO ℕ
  twoTimes die = ⦇ die + die ⦈
