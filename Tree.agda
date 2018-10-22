{-# OPTIONS --allow-unsolved-metas #-}

open import Monad
open import Monad.State
open import LiftProp

-- stdlib {{{

open import Data.List
open import Data.Nat
open import Data.Unit hiding (_≤_)
open import Data.Product
open import Data.Bool
open import Relation.Binary.PropositionalEquality

-- }}}

module Tree where

data Tree (A : Set) : Set where
  leaf : (a : A) → Tree A
  node : Tree A → Tree A → Tree A

-- relabel tree {{{

fresh : State ℕ ℕ
fresh = record { runState = λ n → n , suc n }
-- returning state, and modifying it plus 1 (A × S)

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
  nodesISO : {tal tar : Tree A} → {tbl tbr : Tree B} →
             tal ≅ tbl → tar ≅ tbr →
             node tal tar ≅ node tbl tbr


-- isomorphic trees after relabelling {{{
module LabelIsomorphic where

labelLP≡ : {A : Set} → (t : Tree A) → LiftProp (λ t' → t ≅ t') (label t)
labelLP≡ (leaf a) = ⟦ labelLeafWithProof <> refl ⟧
  where
    labelLeafWithProof = do
                           n ← fresh
                           return (leaf n ,  leafISO)
labelLP≡ (node l r) = let
                        _>>=_ = _>>=LP_
                        return = returnLP
                      in
                      do
                        (l' , pl≡l') ← labelLP≡ l
                        (r' , pr≡r') ← labelLP≡ r
                        return (node l' r' , nodesISO pl≡l' pr≡r')
-- }}}

-- unique labels {{{

module LabelUnique where


record Proof (t : Tree ℕ) (n₁ : ℕ) (n₂ : ℕ) : Set where
  field
    -- n₂NotZero : n₂ ≠ 0
    initial≤final : n₁ ≤ n₂
    -- proofLower : n₁ IsLowerBoundFor t
    -- proofUpper : (pred n₂) IsUpperBoundFor t
    proofNoDups : {!!} t

open Proof public


-- manually (i.e. first defining extended version...) {{{

open import Hoare.Monad

labelX : {A : Set} → (t : Tree A) → StateHoare ℕ (Tree ℕ) λ x x₁ x₂ → ⊤
labelX (leaf a) =
  let
    _>>=_ = _>>=StateHoare_
    return = returnStateHoare
  in
  (
  do
    n ← toStateHoare (fresh)
    return (leaf n)
  )
  concluding
    λ x → tt
labelX (node l r) =
  let
    _>>=_ = _>>=StateHoare_
    return = returnStateHoare
  in
  (
  do
    l' ← (labelX l)
    r' ← (labelX r)
    return (node l' r')
  )
  concluding
    λ x → tt


proof : {A : Set} → (t : Tree A) → label t ≡ forget (labelX t)
proof (leaf a) = refl
proof (node t t₁) = {!!}

-- }}}

-- with lifted operators; retro-actively {{{

open import Hoare.LiftProp

labelLPNoDup : {A : Set} → (t : Tree A) → LiftPropStateHoare Proof (label t)
labelLPNoDup (leaf a) =
  let
    _>>=_ = _>>=StateHoareLP_
    return = returnStateHoareLP
  in
  (
  do
    n ← toStateHoareLP fresh
    return (leaf n)
  )
  ⇒ λ{ (n , s₁ , refl , refl , refl) → {!!}}

labelLPNoDup (node l r) =
  let
    _>>=_ = _>>=StateHoareLP_
    return = returnStateHoareLP
  in
  (
  do
    l' ← labelLPNoDup l
    r' ← labelLPNoDup r
    return (node l' r')
  )
  ⇒ λ{ (l' , s₁ , pl' , r' , s₂ , pr' ) → {!!}}

-- }}}

-- }}}


