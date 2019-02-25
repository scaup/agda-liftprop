module Examples.Password where

open import MonadTC
open import Monads.IO
open import Applicatives.IO
open import Functors.IO
open import Monads.List

open import Data.Nat
open import Relation.Nullary

postulate
  String : Set
  random : ℕ → IO String
  length : String → ℕ
  getLine : IO String

if?_then_else_ : {A P : Set} → Dec P → A → A → A
if? yes p then a else b = a
if? no ¬p then a else b = b

retry : ℕ → IO String
retry 0 = random 20
retry (suc n) = do s ← getLine
                   if? (length s ≥? 20)
                       then (return s)
                       else (retry n)

choosePassword : IO String
choosePassword = retry 3
