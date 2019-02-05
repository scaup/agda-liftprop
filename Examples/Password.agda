module Examples.Password where

open import MonadTC
open import Monads.IO
open import Functors.IO
open import Monads.List

-- stdlib {{{

open import Data.List hiding (length)
open import Data.Nat
open import Function
open import Relation.Nullary.Decidable
open import Relation.Nullary

-- }}}

postulate
  random : ℕ → IO String
  length : String → ℕ

open import Lift.MonadTC using (if?_then_else_)

retry : ℕ → IO String
retry 0 = random 20
retry (suc n) = do s ← getLine
                   if? (length s ≥? 20)
                       then (return s)
                       else (retry n)

choosePassword : IO String
choosePassword = retry 3
