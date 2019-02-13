module Examples.RelabelApplicative where

open import ApplicativeTC
open import FunctorTC
open import Applicatives.State
open import Functors.State

open import Examples.Relabel using (Tree ; fresh)

open Tree

-- stdlib {{{

open import Data.Nat
open import Data.Bool

-- }}}

relabel : {A : Set} → Tree A → State ℕ (Tree ℕ)
relabel (leaf a) = ⦇ leaf fresh ⦈ -- fmap (λ n → leaf n) fresh
relabel (node l r) = ⦇ node (relabel l) (relabel r) ⦈
