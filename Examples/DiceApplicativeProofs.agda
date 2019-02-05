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
  sumBound6IsBound12 : {x y : ℕ} → x ≤ 6 → y ≤ 6 → x + y ≤ 12

genericDieBound6 : Lift (λ a → a ≤ 6) genericDie
genericDieBound6 = {!!}

twoDiceBound12 : Lift (λ a → a ≤ 12) twoDice
twoDiceBound12 = ⦇ (_+_ , λ{ (x , px) (y , py) → sumBound6IsBound12 px py} ) genericDieBound6 genericDieBound6 ⦈

dieBound6twoTimesListBound12 : (dieList : List ℕ) → Lift (λ a → a ≤ 6) dieList → Lift (λ a → a ≤ 12) (twoTimes dieList)
dieBound6twoTimesListBound12 dieList dieListBound6 =
                 ⦇ (_ , λ{ (x , px) (y , py) → sumBound6IsBound12 px py} ) genericDieBound6 genericDieBound6 ⦈
