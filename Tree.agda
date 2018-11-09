{-# OPTIONS --allow-unsolved-metas #-}

open import Monad
open import Monad2Functor
open import Functor
open import Monad.State
open import LiftProp

-- stdlib {{{

open import Data.List
open import Data.Nat
open import Data.Product
open import Data.Bool
open import Relation.Binary.PropositionalEquality

-- }}}

data Tree (A : Set) : Set where
  leaf : (a : A) → Tree A
  node : Tree A → Tree A → Tree A

-- relabel tree {{{

fresh : State ℕ ℕ
runState fresh n = n , suc n -- returning state, and modifying it plus 1 (A × S)

label : {A : Set} → Tree A → State ℕ (Tree ℕ)
label (leaf a) = do
                    n ← fresh
                    return (leaf n)
label (node l r) = do
                        l' ← label l
                        r' ← label r
                        return (node l' r')

-- }}}

-- example trees {{{

exampleTree : Tree Bool
exampleTree = node (leaf true) (node (node (leaf false) (leaf false)) (leaf true))

exampleTree' : Tree Bool
exampleTree' = node (leaf true) (leaf true)

exTree : Tree Bool
exTree = node (node (leaf false) (leaf true)) (node (node (leaf true) (node (leaf false) (leaf true))) (leaf false))

exampleTree'' : Tree ℕ
exampleTree'' = node (leaf 0) (leaf 5)

exTree' : Tree ℕ
exTree' = node (node (leaf 3) (leaf 9)) (node (node (leaf 9) (node (leaf 9) (leaf 9))) (leaf 9))

-- }}}

data _≅_ {A B : Set} : (ta : Tree A) → (tb : Tree B) → Set where
  leafISO : {a : A} → {b : B} → leaf a ≅ leaf b
  nodesISO : {tal tar : Tree A} → {tbl tbr : Tree B} → tal ≅ tbl → tar ≅ tbr → node tal tar ≅ node tbl tbr

pro : exTree' ≅ exTree
pro = nodesISO (nodesISO leafISO leafISO) (nodesISO (nodesISO leafISO (nodesISO leafISO leafISO)) leafISO)

-- isomorphic trees after relabelling {{{

labelLP≡ : {A : Set} → (t : Tree A) → LiftProp (λ t' → t ≅ t') (label t)
monadicValueX (labelLP≡ (leaf a)) = do
                                       n ← fresh
                                       return (leaf n ,  leafISO)
proofPPE (labelLP≡ (leaf a)) = refl
labelLP≡ (node l r) = let
                        _>>=_ = _>>=LP'_
                        return = returnLP'
                      in
                      do
                        pl≡l' ← labelLP≡ l
                        pr≡r' ← labelLP≡ r
                        return (nodesISO pl≡l' pr≡r')

-- }}}

-- suggestion to specialize LiftProp to state with hoare state {{{

record StateDX (S : Set) (A : Set) (P : A → S → S → Set) : Set where
  field
    runStateDX : (s₁ : S) → Σ (A × S) λ{(a , s₂) → P a s₁ s₂}

open StateDX


forgetDX : ∀{S A P} → StateDX S A P → State S A
runState (forgetDX record { runStateDX = k }) s = proj₁ (k s)


record LiftPropStateD {A S : Set} (P : A → S → S → Set) (stateComputation : State S A) : Set where
  constructor _,_
  field
    stateComputationDX : StateDX S A P
    proofPPE : stateComputation ≡ forgetDX stateComputationDX

labelLPUniqueLabels : {A : Set} → (t : Tree A) → LiftPropStateD {!!} (label t)
labelLPUniqueLabels t = {!!}

_>>=LPDS_ : {!!}
_>>=LPDS_ = {!!}

-- }}}
