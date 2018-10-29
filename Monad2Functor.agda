module Monad2Functor where

-- stdlib {{{

open import Functor
open import Monad

open import Data.Nat
open import Postulates
open import Data.List
open import Data.Bool hiding (_≟_; _∧_)
open import Data.Product
open import Data.Unit hiding (_≟_; _≤?_; _≤_)
open import Data.Empty
open import Data.Sum
open import Function

open import Relation.Unary using (Decidable)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- }}}

instance
  Ω : {M : Set → Set} → {{ Mimp : Monad M }} → Functor M
  Functor.fmap (Ω {M} ⦃ record { return = return ;
                               _>>=_ = _>>=_ ;
                               leftId = leftId ;
                               rightId = rightId ;
                               assoc = assoc } ⦄) f mx = mx >>= (return ∘ f)
  Functor.unit (Ω {M} ⦃ record { return = return ;
                               _>>=_ = _>>=_ ;
                               leftId = leftId ;
                               rightId = rightId ;
                               assoc = assoc } ⦄) = rightId _
  Functor.composition (Ω {M} ⦃ record { return = return ;
                                    _>>=_ = _>>=_ ;
                                    leftId = leftId ;
                                    rightId = rightId ;
                                    assoc = assoc } ⦄) g f mx = begin
                                                                  mx >>= (return ∘ f ∘ g)
                                                                ≡⟨ cong (_>>=_ mx) (sym (funext (λ x → leftId _ _))) ⟩
                                                                  mx >>= (λ x → return (g x) >>= (return ∘ f))
                                                                ≡⟨ sym (assoc _ _ _) ⟩
                                                                  ((mx >>= (return ∘ g)) >>= (return ∘ f)) ∎

fmap->>= : {M : Set → Set} → {{ Mimp : Monad M }} → {A B C : Set} →
  (g : B → M C) → (f : A → B) → (mx : M A) → fmap f mx >>= g ≡ mx >>= (g ∘ f)
fmap->>= g f mx = begin
                    fmap f mx >>= g
                  ≡⟨ assoc _ _ _ ⟩
                    mx >>= (λ x → return (f x) >>= g)
                  ≡⟨ cong (_>>=_ mx) (funext (leftId g ∘ f)) ⟩
                    mx >>= (g ∘ f)
                  ∎

