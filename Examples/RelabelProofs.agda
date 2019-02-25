module Examples.RelabelProofs where
open import Examples.Relabel using (Tree ; fresh)
open Tree

module Isomoporhic where

  open import Functors.State
  open import Applicatives.State
  open import Monads.State
  open import MonadLift renaming (_>>=L_ to _>>=_; returnL to return)
  open import ApplicativeLift renaming (_<*>L_ to _<*>_ ; pureL to pure)
  open import FunctorLift

  data _≅_ {A B : Set} : Tree A → Tree B → Set where
    leafISO : {a : A} → {b : B} → leaf a ≅ leaf b
    nodesISO : {tal tar : Tree A} →
               {tbl : Tree B} → tal ≅ tbl →
               {tbr : Tree B} → tar ≅ tbr →
               node tal tar ≅ node tbl tbr


  module WithMonad where
    open Examples.Relabel.WithMonad
    open import MonadLift renaming (_>>=L_ to _>>=_; returnL to return)

    relabel≅ : {A : Set} → (t : Tree A) → Lift (λ t' → t ≅ t') (relabel t)
    relabel≅ (leaf a) = do
                          (n , _) ← nothing2Prove fresh
                          return (leaf n , leafISO)
    relabel≅ (node l r) = do
                            (l' , pl≡l') ← relabel≅ l
                            (r' , pr≡r') ← relabel≅ r
                            return (node l' r' , nodesISO pl≡l' pr≡r')



  module WithApplicative where
    open Examples.Relabel.WithApplicative
    open import ApplicativeLift renaming (_<*>L_ to _<*>_ ; pureL to pure)

    relabel≅ : {A : Set} → (t : Tree A) → Lift (λ t' → t ≅ t') (relabel t)
    relabel≅ (leaf a) = ⦇ (λ _ → leafISO) (nothing2Prove fresh) ⦈
    relabel≅ (node l r) = ⦇ nodesISO (relabel≅ l) (relabel≅ r) ⦈

  module WithApplicativeAndFmap where
    open Examples.Relabel.WithApplicativeAndFmap
    open import ApplicativeLift renaming (_<*>L_ to _<*>_ ; pureL to pure)

    relabel≅ : {A : Set} → (t : Tree A) → Lift (λ t' → t ≅ t') (relabel t)
    relabel≅ (leaf a) = fmapL (λ _ → leafISO) (nothing2Prove fresh)
    relabel≅ (node l r) = ⦇ nodesISO (relabel≅ l) (relabel≅ r) ⦈

module NoDuplicates where
  open import Data.Nat
  open import Data.Product
  open Examples.Relabel.WithMonad
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

  open import Exp.Hoare
  open import Function

  relabelN : {A : Set} → (t : Tree A) → Hoare ℕ (Tree ℕ) StrongerResult
  relabelN (leaf a) = (toHoare fresh >>=H (returnH ∘ leaf)) ⇒H λ x → {!!}
  relabelN (node l r) = (relabelN l >>=H λ l' →
                         relabelN r >>=H λ r' →
                         returnH (node l' r')) ⇒H {!!}

  open import Exp.HoareLift using (forget)
  open import Relation.Binary.PropositionalEquality
  open import Postulates
  test : {A : Set} → (t : Tree A) → forget (relabelN t) ≡ relabel t
  test (leaf a) = refl
  test (node t t₁) = funext λ a → {!!}

  open import Exp.HoareLift renaming (_>>=L_ to _>>=_ ; returnL to return)

  relabelNoDups : {A : Set} → (t : Tree A) → Lift StrongerResult (relabel t)
  relabelNoDups (leaf a) = (do
                               n ← toL fresh
                               return (leaf n)
                           ) ⇒ λ{ (n , s₁ , refl , refl , refl) → {!!}}
  relabelNoDups (node l r) = (do
                                 {- s₁ -} l' {- s₂ -} ← relabelNoDups l
                                 {- s₂ -} r' {- s₃ -} ← relabelNoDups r
                                          return (node l' r')
                             ) ⇒ λ{ (l' , s₂ , pl' , r' , s₃ , pr' , refl , refl) → {!!}}
