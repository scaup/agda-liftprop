module Functors.List where

open import Data.List hiding (filter)

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Function

module FunctorImp where
  fmap : {X Y : Set} → (f : X → Y) → List X → List Y
  fmap f [] = []
  fmap f (x ∷ xs) = f x ∷ fmap f xs

  composition : ∀{A B C} → (g : A → B) → (f : B → C) → (as : List A) → fmap (f ∘ g) as ≡ fmap f (fmap g as)
  composition g f [] = refl
  composition g f (x ∷ as) = cong (_∷_ (f (g x))) (composition g f as)

  unit : ∀{A} {as : List A} → fmap id as ≡ as
  unit {_} {[]} = refl
  unit {_} {x ∷ as} = cong (_∷_ x) unit

open import FunctorTC

instance
  listFunctor : Functor List
  listFunctor = record { fmap = FunctorImp.fmap ;
               composition = FunctorImp.composition ;
               unit = FunctorImp.unit }


fmapAssoc : {A B : Set} → {f : A → B} → (as as' : List A) →
           fmap f (as ++ as') ≡ fmap f as ++ fmap f as'
fmapAssoc [] as' = refl
fmapAssoc (x ∷ as) as' = cong (_∷_ _) (fmapAssoc as as')
