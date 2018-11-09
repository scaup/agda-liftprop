module LiftProp.IO where

open import LiftProp
open import Monad.IO

postulate
  _∧LPio_ : {A : Set} → {ioa : IO A} → {P Q : Predicate A} →
            LiftProp P ioa → LiftProp Q ioa → LiftProp (P ∧ Q) ioa
