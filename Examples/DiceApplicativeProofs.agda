module Examples.DiceApplicativeProofs where

open import Examples.DiceApplicative

open import Functors.IO
open import Functors.List
open import Applicatives.List
open import Lift
open import Lift.ApplicativeTC renaming (_<*>L_ to _<*>_; pureL to pure)
open import Postulates

-- stdlib {{{

open import Relation.Binary.PropositionalEquality
open import Data.List
open import Data.Nat
open import Data.Product

-- }}}

postulate
  sumBound6IsBound12 : {x : ℕ} → x ≤ 6 → ∀ {y} → y ≤ 6 → x + y ≤ 12
  sumBound6IsBound12Natural : {x y : ℕ} → x ≤ 6 → y ≤ 6 → x + y ≤ 12

genericDieBound6 : Lift (λ a → a ≤ 6) genericDie
genericDieBound6 = rangeUpBound 1 6

twoDiceBound12 : Lift (λ a → a ≤ 12) twoDice
twoDiceBound12 = ⦇ (sumBound6IsBound12) genericDieBound6 genericDieBound6 ⦈

dieBound6twoTimesListBound12 : (dieList : List ℕ) → Lift (λ a → a ≤ 6) dieList →
                               Lift (λ a → a ≤ 12) (twoTimes dieList)
dieBound6twoTimesListBound12 dieList dieListBound6 =
                 ⦇ (λ p p₁ → sumBound6IsBound12Natural p p₁) dieListBound6 dieListBound6 ⦈
