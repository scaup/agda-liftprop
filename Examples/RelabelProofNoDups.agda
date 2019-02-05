module Examples.RelabelProofNoDups where

open import Examples.Relabel

open import Monads.IO
open import Functors.IO
open import Functors.State
open import Monads.State
open import Lift
open import Lift.MonadTC renaming (_>>=L_ to _>>=_; returnL to return)
open import Postulates

-- stdlib {{{

open import Data.List
open import Data.Nat
open import Data.Product

-- }}}

postulate
  _IsLowerBoundFor_ : ℕ → Tree ℕ → Set
  _IsUpperBoundFor_ : ℕ → Tree ℕ → Set
  NoDups : Tree ℕ → Set

record NoDupsAndBounds (t : Tree ℕ) (n₁ : ℕ) (n₂ : ℕ) : Set where
  field
    initial≤final : n₁ ≤ n₂
    proofLower : n₁ IsLowerBoundFor t
    proofUpper : (pred n₂) IsUpperBoundFor t
    proofNoDups : NoDups t

postulate
  f : {n₁ n₂ n₃ : ℕ} {l' : Tree ℕ} → {r' : Tree ℕ} →
      NoDupsAndBounds l' n₁ n₂ → NoDupsAndBounds r' n₂ n₃ →
      NoDupsAndBounds (node l' r') n₁ n₃
