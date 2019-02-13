module Examples.RelabelApplicativeProofIsomorphic where

open import ApplicativeTC hiding (_<*>_ ; pure)
open import FunctorTC
open import Applicatives.State
open import Functors.State

open import Lift
open import Lift.ApplicativeTC renaming (_<*>L_ to _<*>_ ; pureL to pure)

open import Examples.Relabel using (Tree ; fresh)
open import Examples.RelabelApplicative using (relabel)
open import Examples.RelabelProofIsomorphic using (_≅_)

open Tree
open _≅_

-- stdlib {{{

open import Function
open import Data.Nat
open import Data.Bool
open import Data.Product
open import Data.Unit

-- }}}

relabel≅ : {A : Set} → (t : Tree A) → Lift (λ t' → t ≅ t') (relabel t)
relabel≅ (leaf a) = ⦇ (λ _ → leafISO) (nothing2Prove fresh) ⦈
relabel≅ (node l r) = ⦇ (λ p p₁ → nodesISO p p₁) (relabel≅ l) (relabel≅ r) ⦈
