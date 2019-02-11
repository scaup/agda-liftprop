module Examples.DiceApplicative where

open import ApplicativeTC
open import Applicatives.List

-- stdlib {{{

open import Data.List
open import Data.Nat

-- }}}

genericDie = 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ []

twoDice : List ℕ
twoDice = ⦇ _+_ genericDie genericDie ⦈

twoTimes : List ℕ → List ℕ
twoTimes die = ⦇ die + die ⦈
