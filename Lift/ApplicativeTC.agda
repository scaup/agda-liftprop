{-# OPTIONS --allow-unsolved-metas #-}

module Lift.ApplicativeTC where

open import Lift
open import ApplicativeTC

open import Postulates

-- stdlib {{{

open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- }}}



pureL : {A : Set → Set} → {{ _ : Applicative A }} →
           {X : Set} → {P : X → Set} →
           (xp : Σ X P) → Lift {X} {A} P (pure (proj₁ xp))
witness (pureL xp) = pure xp
corresponds (pureL (x , p)) = sym $
  begin
    fmap proj₁ (pure (x , p))
  ≡⟨ compatiblefmapA ⟩
    pure proj₁ <*> (pure (x , p))
  ≡⟨ homomorphism proj₁ (x , p) ⟩
    pure x ∎

pureL' : {A : Set → Set} → {{ _ : Applicative A }} →
           {X : Set} → {P : X → Set} →
           {x : X} → (p : P x) → Lift {X} {A} P (pure x)
pureL' p = pureL (_ , p)

_<*>L_ : {A : Set → Set} → {{ _ : Applicative A }} →
         {X Y : Set} → {P : Predicate X} → {Q : Predicate Y} →
         {af : A (X → Y)} → {ax : A X} →
           Lift (λ f → (xp : Σ X P) → Q (f (proj₁ xp))) af → Lift P ax → Lift Q (af <*> ax)
witness (lfs <*>L lp) = fmapR (λ{ (f , pf) → λ{ (x , p) → (f x) , pf (x , p) }}) lfs <*> witness lp
corresponds (lfs <*>L lp) = {!!}

_<*>L'_ : {A : Set → Set} → {{ _ : Applicative A }} →
          {X Y : Set} → {P : Predicate X} → {Q : Predicate Y} →
          {af : A (X → Y)} → {ax : A X} →
            Lift (λ f → {x : X} → (p : P x) → Q (f x)) af → Lift P ax → Lift Q (af <*> ax)
lfs <*>L' lp = {!!}
