module Examples.ListFunctionsProofs where

open import Examples.ListFunctions

open import Functors.List
open import FunctorTC
open import FunctorLift

open import Data.Bool renaming (_∧_ to _&&_; _∨_ to _||_)
open import Data.List hiding (filter)
open import Data.Nat hiding (_≟_)
open import Data.Nat.Properties hiding (_≟_)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary

[]L : {A : Set} → {P : Predicate A} → Lift {List} P ([])
[]L = record { witness = [] ; corresponds = refl }

_∷L_ : {A : Set} → {P : Predicate A} → {xs : List A} →
  {a : A} → (P a) → Lift P xs → Lift P (a ∷ xs)
pa ∷L record { witness = xs ; corresponds = refl } =
  record { witness = (_ , pa) ∷ xs ; corresponds = refl }

invertP-cons : ∀ {A} {P : Predicate A} {x} {xs} → Lift P (x ∷ xs) → P x × (Lift P xs)
invertP-cons record { witness = [] ; corresponds = () }
invertP-cons record { witness = ((x , p) ∷ xps) ; corresponds = refl } = p , record { witness = xps ; corresponds = refl }

[_]L : {A : Set} → {P : Predicate A} → {a : A} → P a → Lift P [ a ]
[_]L pa = pa ∷L []L

filterPreserves : {A : Set} → {P : A → Set} → {as : List A} →
  (f : A → Bool) → Lift P as → Lift P (filter f as)
filterPreserves {as = []} f = id
filterPreserves {as = x ∷ xs} f xxsP with invertP-cons xxsP
filterPreserves {as = x ∷ xs} f xxsP | px , xsP with f x ≟ true
filterPreserves {as = x ∷ xs} f xxsP | px , xsP | yes p = px ∷L filterPreserves f xsP
filterPreserves {as = x ∷ xs} f xxsP | px , xsP | no ¬p = filterPreserves f xsP

filterNew : {A : Set} →
  (f : A → Bool) → (as : List A) → Lift (λ a → f a ≡ true) (filter f as)
filterNew f [] = []L
filterNew f (x ∷ as) with (f x) ≟ true
filterNew f (x ∷ as) | yes p = p ∷L filterNew f as
filterNew f (x ∷ as) | no ¬p = filterNew f as

_++L_ : ∀{A P} → {xs ys : List A} → Lift P xs → Lift P ys → Lift P (xs ++ ys)
_++L_ {xs = []} {ys} []P ysP = ysP
_++L_ {xs = a ∷ as} {ys} aasP ysP with invertP-cons aasP
_++L_ {xs = a ∷ as} {ys} aasP ysP | pa , asP = pa ∷L (asP ++L ysP)

_,L_ : {A : Set} → {as : List A} → {P Q : Predicate A} →
            Lift P as → Lift Q as → Lift (P ∧ Q) as
_,L_ {as = []} []P []Q = []L
_,L_ {as = x ∷ xs} xxsP xxsQ with invertP-cons xxsP | invertP-cons xxsQ
_,L_ {_} {x ∷ xs} xxsP xxsQ | px , xsP | qx , xsQ = (px , qx) ∷L (xsP ,L xsQ)

rangeUpBound : (d : ℕ) → (u : ℕ) → Lift (λ x → x ≤ u) (range d u)
rangeUpBound zero zero = [ z≤n ]L
rangeUpBound (suc d) zero = []L
rangeUpBound zero (suc u) =
  applyL ≤-step (rangeUpBound zero u) ++L [ ≤-refl ]L
rangeUpBound (suc d) (suc u) = fmapL s≤s (rangeUpBound d u)

rangeDownBound : (d : ℕ) → (u : ℕ) → Lift (λ x → d ≤ x) (range d u)
rangeDownBound zero zero = [ z≤n ]L
rangeDownBound (suc n) zero = []L
rangeDownBound zero (suc m) = rangeDownBound zero m ++L [ z≤n ]L
rangeDownBound (suc n) (suc m) = fmapL s≤s (rangeDownBound n m)


indList : {A : Set} (C : List A → Set) (c[] : C []) (c∷ : (x : A) (xs : List A) → C xs → C (x ∷ xs)) (as : List A) → C as
indList C c[] c∷ [] = c[]
indList C c[] c∷ (x ∷ as) = c∷ x as (indList C c[] c∷ as)

indListL : {A : Set} {P : Predicate A} (C : (xs : List A) → Lift P xs → Set)
           (c[] : C [] []L)
           (c∷ : ∀{x : A}(px : P x){xs : List A}(pxs : Lift P xs) → C xs pxs → C (x ∷ xs) (px ∷L pxs))
           {as : List A}(pas : Lift P as) → C as pas
indListL C c[] c∷ {[]} record { witness = [] ; corresponds = refl } = c[]
indListL C c[] c∷ {[]} record { witness = (x ∷ witness₁) ; corresponds = () }
indListL C c[] c∷ {x ∷ as} record { witness = [] ; corresponds = () }
indListL C c[] c∷ {.(proj₁ xpx) ∷ .(fmap proj₁ xpxs)} record { witness = (xpx ∷ xpxs) ; corresponds = refl } =
  c∷ (proj₂ xpx) (record { witness = xpxs ; corresponds = refl })
     (indListL C c[] c∷ (record { witness = xpxs ; corresponds = refl }))

{- PSUEDO-CODE

_++L_ : ∀{A P} → {xs ys : List A} → Lift P xs → Lift P ys → Lift P (xs ++ ys)
_++L_ {xs = xs} xsP ysP  by indListL xsP
_++L_ {xs = []} []L ysP  = ysP
_++L_ {xs = a ∷ as} (px ∷L asP) ysP = pa ∷L (asP ++L ysP)

-}
