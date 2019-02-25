{-# OPTIONS --allow-unsolved-metas #-}

module Examples.Relabel where

open import MonadTC
open import ApplicativeTC
open import FunctorTC
open import Monads.State
open import Applicatives.State
open import Functors.State

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

module WithMonad where
  relabel : {A : Set} → Tree A → State ℕ (Tree ℕ)
  relabel (leaf a) = do
                      n ← fresh
                      return (leaf n)
  relabel (node l r) = do
                          l' ← relabel l
                          r' ← relabel r
                          return (node l' r')

module WithApplicative where
  relabel : {A : Set} → Tree A → State ℕ (Tree ℕ)
  relabel (leaf a) = ⦇ leaf fresh ⦈
  relabel (node l r) = ⦇ node (relabel l) (relabel r) ⦈

module WithApplicativeAndFmap where
  relabel : {A : Set} → Tree A → State ℕ (Tree ℕ)
  relabel (leaf a) = fmap (λ n → leaf n) fresh
  relabel (node l r) = ⦇ node (relabel l) (relabel r) ⦈
