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
  Functor.composition listFunctor g f (x ∷ as) = cong (_∷_ (f (g x))) (composition g f as)
  Functor.unit listFunctor {A} {[]} = refl
  Functor.unit listFunctor {A} {x ∷ fa} = cong (_∷_ x) unit

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

[]L : {A : Set} → {P : Predicate A} → Lift P (the (List A) [])
[]L = record { witness = [] ; corresponds = refl }

_∷L_ : {A : Set} → {P : Predicate A} → {xs : List A} →
  {a : A} → (P a) → Lift P xs → Lift P (a ∷ xs)
pa ∷L record { witness = xs ; corresponds = refl } =
  record { witness = (_ , pa) ∷ xs ; corresponds = refl }

invertP-cons : ∀ {A} {P : Predicate A} {x} {xs} → Lift P (x ∷ xs) → P x × (Lift P xs)
invertP-cons lp with destruct lp
  where
   destruct : {A : Set} → {P : Predicate A} → {xs : List A} → Lift P xs → xs ≡ [] ⊎ Σ[ a ∈ A ] P a × Σ[ t ∈ List A ] Lift P t × (xs ≡ a ∷ t)
   destruct record { witness = [] ; corresponds = corresponds } = inj₁ corresponds
   destruct record { witness = ((x , px) ∷ xs) ; corresponds = refl } =
     inj₂ (x , px , fmap proj₁ xs , record { witness = xs ; corresponds = refl } , refl)
invertP-cons lp | inj₁ ()
invertP-cons lp | inj₂ (a , pa , as , asP , refl) = pa , asP

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
