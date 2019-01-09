module Examples.Dice where

open import MonadTC
open import Monads.IO
open import Monads.List

-- stdlib {{{

open import Data.List
open import Data.Nat

-- }}}

postulate
  genericDie : IO ℕ

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
