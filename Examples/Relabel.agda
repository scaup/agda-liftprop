{-# OPTIONS --allow-unsolved-metas #-}

module Examples.Relabel where

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

fresh : State ℕ ℕ
fresh = do
          n ← get
          modify suc
          return n

relabel : {A : Set} → Tree A → State ℕ (Tree ℕ)
relabel (leaf a) = do
                    n ← fresh
                    return (leaf n)
relabel (node l r) = do
                        l' ← relabel l
                        r' ← relabel r
                        return (node l' r')


exampleTree : Tree Bool
exampleTree = node (leaf true) (node (node (leaf false) (leaf false)) (leaf true))

exampleTreeRelabelled : Tree ℕ
exampleTreeRelabelled = node (leaf 5) (node (node (leaf 6) (leaf 7)) (leaf 8))

data _≅_ {A B : Set} : Tree A → Tree B → Set where
  leafISO : {a : A} → {b : B} → leaf a ≅ leaf b
  nodesISO : {tal tar : Tree A} → {tbl tbr : Tree B} → tal ≅ tbl → tar ≅ tbr → node tal tar ≅ node tbl tbr

isomorphicEx : exampleTree ≅ exampleTreeRelabelled
isomorphicEx = nodesISO leafISO (nodesISO (nodesISO leafISO leafISO) leafISO)


{-




-- isomorphic trees after relabelling {{{


-- }}}

-- noduplicates {{{

postulate
  _IsLowerBoundFor_ : ℕ → Tree ℕ → Set
  _IsUpperBoundFor_ : ℕ → Tree ℕ → Set
  NoDuplicates : Tree ℕ → Set

record StrongerResult (t : Tree ℕ) (n₁ : ℕ) (n₂ : ℕ) : Set where
  field
    initial≤final : n₁ ≤ n₂
    proofLower : n₁ IsLowerBoundFor t
    proofUpper : (pred n₂) IsUpperBoundFor t
    proofNoDups : NoDuplicates t

postulate
  f : {n₁ n₂ n₃ : ℕ} {l' : Tree ℕ} → {r' : Tree ℕ} →
      StrongerResult l' n₁ n₂ → StrongerResult r' n₂ n₃ →
      StrongerResult (node l' r') n₁ n₃



-- }}}
-}
