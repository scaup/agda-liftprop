module Examples.DiceProofs where

open import Examples.Dice

open import Monads.IO
open import Functors.IO
open import Functors.List
open import Monads.List
open import Lift
open import Lift.MonadTC renaming (_>>=L_ to _>>=_; returnL to return)
open import Postulates

-- stdlib {{{

open import Data.List
open import Data.Nat
open import Data.Product

-- }}}

postulate
  sumBound6IsBound12 : {x y : ℕ} → x ≤ 6 → y ≤ 6 → x + y ≤ 12

  genericDieBound6 : Lift (λ x → x ≤ 6) genericDie

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

