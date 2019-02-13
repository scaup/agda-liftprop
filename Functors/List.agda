{-# OPTIONS --allow-unsolved-metas #-}

module Functors.List where

open import FunctorTC
open import Lift
open import SmallThings

open import Data.List hiding (filter)

-- sdllib {{{

open import Data.Product
open import Data.Nat hiding (_≟_)
open import Data.Nat.Properties hiding (_≟_)
open import Relation.Nullary
open import Function
open import Data.Bool hiding (_∧_)
open import Data.Sum
open import Relation.Binary.PropositionalEquality hiding ([_])

-- }}}

instance
  listFunctor : Functor List
  Functor.fmap listFunctor f [] = []
  Functor.fmap listFunctor f (x ∷ xs) = f x ∷ fmap f xs
  Functor.composition listFunctor g f [] = refl
  Functor.composition listFunctor g f (x ∷ xs) = cong (λ zs → f (g x) ∷ zs) (Functor.composition listFunctor g f xs)
  Functor.unit listFunctor {fa = []} = refl
  Functor.unit listFunctor {fa = x ∷ xs} = cong (λ xs → x ∷ xs) (Functor.unit listFunctor)

filter : {A : Set} → (A → Bool) → List A → List A
filter f [] = []
filter f (x ∷ xs) with f x ≟ true
filter f (x ∷ xs) | yes _ = x ∷ filter f xs
filter f (x ∷ xs) | no _ = filter f xs

range : ℕ → ℕ → List ℕ
range zero zero = [ 0 ]
range (suc n) zero = []
range zero (suc m) = range zero m ++ [ suc m ]
range (suc n) (suc m) = fmap suc (range n m)

-- Primitives to work with Lift over List {{{

[]L : {A : Set} → {P : Predicate A} → Lift P (the (List A) [])
[]L = record { witness = [] ; corresponds = refl }

_∷L_ : {A : Set} → {P : Predicate A} → {xs : List A} →
  (ap : Σ A P) → Lift P xs → let (a , p) = ap in Lift P (a ∷ xs)
(a , p) ∷L record { witness = xs ; corresponds = refl } =
  record { witness = (a , p) ∷ xs ; corresponds = refl }

destruct : {A : Set} → {P : Predicate A} → {xs : List A} → Lift P xs → xs ≡ [] ⊎ Σ[ a ∈ A ] P a × Σ[ t ∈ List A ] Lift P t × (xs ≡ a ∷ t)
destruct record { witness = [] ; corresponds = corresponds } = inj₁ corresponds
destruct record { witness = ((x , px) ∷ xs) ; corresponds = refl } = inj₂ (x , px , fmap proj₁ xs , record { witness = xs ; corresponds = refl } , refl)

indList : {A : Set} (C : List A → Set) (c[] : C []) (c∷ : (x : A) (xs : List A) → C xs → C (x ∷ xs)) (as : List A) → C as
indList C c[] c∷ [] = c[]
indList C c[] c∷ (x ∷ as) = c∷ x as (indList C c[] c∷ as)

indListL' : {A : Set} {P : Predicate A} (C : (xs : List A) → Lift P xs → Set)
           (c[] : C [] []L)
           (c∷ : ∀{x : A}(px : P x){xs : List A}(pxs : Lift P xs) → C xs pxs → C (x ∷ xs) ((x , px) ∷L pxs))
           {as : List A}(pas : Lift P as) → C as pas
indListL' C c[] c∷ {[]} record { witness = [] ; corresponds = refl } = c[]
indListL' C c[] c∷ {[]} record { witness = (x ∷ witness₁) ; corresponds = () }
indListL' C c[] c∷ {x ∷ as} record { witness = [] ; corresponds = () }
indListL' C c[] c∷ {.(proj₁ xpx) ∷ .(fmap proj₁ xpxs)} record { witness = (xpx ∷ xpxs) ; corresponds = refl } =
  c∷ (proj₂ xpx) (record { witness = xpxs ; corresponds = refl })
     (indListL' C c[] c∷ (record { witness = xpxs ; corresponds = refl }))

hdL : {A : Set} {P : Predicate A} {a : A} {as : List A} → Lift P (a ∷ as) → P a
hdL {A} {P} {a} {as} record { witness = [] ; corresponds = () }
hdL {A} {P} {.(proj₁ xpx)} {.(fmap proj₁ xpxs)} record { witness = (xpx ∷ xpxs) ; corresponds = refl } = proj₂ xpx

tlL : {A : Set} {P : Predicate A} {a : A} {as : List A} → Lift P (a ∷ as) → Lift P as
tlL {A} {P} {a} {as} record { witness = [] ; corresponds = () }
tlL {A} {P} {.(proj₁ xpx)} {.(fmap proj₁ xpxs)} record { witness = (xpx ∷ xpxs) ; corresponds = refl } =
  record { witness = xpxs ; corresponds = refl }

-- }}}

-- Derived forms

[_]L : {A : Set} → {P : Predicate A} → {a : A} → P a → Lift P [ a ]
[_]L pa = (_ , pa) ∷L []L

filterPreserves : {A : Set} → {P : A → Set} → {as : List A} →
  (f : A → Bool) → Lift P as → Lift P (filter f as)
filterPreserves f lp with destruct lp
filterPreserves f lp | inj₁ refl = []L
filterPreserves f lp | inj₂ (x , px , xs , xsP , refl) with f x ≟ true
filterPreserves f lp | inj₂ (x , px , xs , xsP , refl) | yes p = (x , px) ∷L filterPreserves f xsP
filterPreserves f lp | inj₂ (x , px , xs , xsP , refl) | no ¬p = filterPreserves f xsP

filterNew : {A : Set} →
  (f : A → Bool) → (as : List A) → Lift (λ a → f a ≡ true) (filter f as)
filterNew f [] = []L
filterNew f (x ∷ as) with (f x) ≟ true
filterNew f (x ∷ as) | yes p = (_ , p) ∷L filterNew f as
filterNew f (x ∷ as) | no ¬p = filterNew f as

_++L_ : ∀{A P} → {xs ys : List A} → Lift P xs → Lift P ys → Lift P (xs ++ ys)
xsP ++L ysP with destruct xsP
(xsP ++L ysP) | inj₁ refl = ysP
(xsP ++L ysP) | inj₂ (x , px , xs' , xs'P , refl) = (x , px) ∷L (xs'P ++L ysP)

_,L_ : {A : Set} → {as : List A} → {P Q : Predicate A} →
            Lift P as → Lift Q as → Lift (P ∧ Q) as
xsP ,L xsQ with destruct xsP | destruct xsQ
(xsP ,L xsQ) | inj₁ refl | inj₁ x = []L
(xsP ,L xsQ) | inj₁ refl | inj₂ (_ , _ , _ , _ , ())
(xsP ,L xsQ) | inj₂ (_ , _ , _ , _ , refl) | inj₁ ()
(xsP ,L xsQ) | inj₂ (x , px , xs' , xs'P , refl) | inj₂ (.x , qx , .xs' , xs'Q , refl) =
  (x , px , qx) ∷L (xs'P ,L xs'Q)

rangeUpBound : (d : ℕ) → (u : ℕ) → Lift (λ x → x ≤ u) (range d u)
rangeUpBound zero zero = [ z≤n ]L
rangeUpBound (suc d) zero = []L
rangeUpBound zero (suc u) =
  applyL ≤-step (rangeUpBound zero u) ++L [ ≤-refl ]L
rangeUpBound (suc d) (suc u) = fmapL' s≤s (rangeUpBound d u)

rangeDownBound : (d : ℕ) → (u : ℕ) → Lift (λ x → d ≤ x) (range d u)
rangeDownBound zero zero = [ z≤n ]L
rangeDownBound (suc n) zero = []L
rangeDownBound zero (suc m) = rangeDownBound zero m ++L [ z≤n ]L
rangeDownBound (suc n) (suc m) = fmapL' s≤s (rangeDownBound n m)
