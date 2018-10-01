-- open import Imports

open import Postulates

-- stdlib {{{

open import Data.Nat
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

-- "Typeclass" monad with monadic laws

record Monad (M : Set → Set) : Set₁ where
  field
    return : {X : Set} → X → M X
    _>>=_ : {X Y : Set} → (M X) → (X → M Y) → (M Y)
    leftId : {X Y : Set} → (f : X → M Y) → (x : X) →
             return x >>= f ≡ f x
    rightId : {X : Set} → (m : M X) →
              m >>= return ≡ m
    assoc : {X Y Z : Set} → (g : X → M Y) → (f : Y → M Z) → (mx : M X) →
            (mx >>= g) >>= f ≡ mx >>= (λ x → g x >>= f)

open Monad {{...}} public

_>>_ : {M : Set → Set} → {{ Mimp : Monad M }} → {X Y : Set} → M X → M Y → M Y
mx >> my = mx >>= λ _ → my

-- Monads are functors

fmap : {M : Set → Set} → {{ Mimp : Monad M }} → {X Y : Set} → (X → Y) → M X → M Y
fmap f mx = mx >>= (return ∘ f)

law-unit : {M : Set → Set} → {{ Mimp : Monad M }} → {A : Set} → {ma : M A} → fmap {X = A} {Y = A} id ma ≡ ma
law-unit {M} {{Mimp}} {A} {ma} = rightId ma

law-composition : {M : Set → Set} → {{ Mimp : Monad M }} → {A B C : Set} → (g : A → B) → (f : B → C) → (fa : M A) → fmap (f ∘ g) fa ≡ (fmap f ∘ fmap g) fa
law-composition {M} {{ Mimp }} {A} {B} {C} g f ma with Monad.leftId Mimp (λ x → return (f x)) | Monad.rightId Mimp | sym (Monad.assoc Mimp {A} {B} {C} (λ x → return (g x)) (λ x → return (f x)) ma)
law-composition {M} {{ Mimp }} {A} {B} {C} g f ma | eq | eq2 | eq3 = begin
                                                                       (ma >>= (λ x → return (f (g x))))
                                                                     ≡⟨ cong (λ x → ma >>= x) (funext λ a → (sym (eq (g a))) ) ⟩
                                                                       (ma >>= (λ x → return (g x) >>= (λ x₁ → return (f x₁))))
                                                                     ≡⟨ eq3 ⟩
                                                                       Monad._>>=_ Mimp
                                                                         (Monad._>>=_ Mimp ma (λ x → Monad.return Mimp (g x)))
                                                                         (λ x → Monad.return Mimp (f x)) ∎

fmap->>= : {M : Set → Set} → {{ Mimp : Monad M }} → {A B C : Set} → (g : B → M C) → (f : A → B) → (mx : M A) → fmap f mx >>= g ≡ mx >>= (g ∘ f)
fmap->>= g f mx = begin
                    fmap f mx >>= g
                  ≡⟨ assoc _ _ _ ⟩
                    mx >>= (λ x → return (f x) >>= g)
                  ≡⟨ cong (_>>=_ mx) (funext (leftId g ∘ f)) ⟩
                    mx >>= (g ∘ f)
                  ∎

-- Display pragmas


-- dependently typed version of mfilter in haskell

{-
mfilter : {A : Set} → {M : Set → Set} → {{ Mimp : Monad M }} → {P : A → Set} →
  (P? : Decidable P) → M A → M A
mfilter {A} {M} P? ma =
  ma >>= f
  where
    f : A → M A
    f a with P? a
    f a | yes p = {!!}
    f a | no ¬p = {!!}
-}


{-# DISPLAY Monad._>>=_ imp a b = a >>= b #-}
{-# DISPLAY Monad.return i a = return a #-}
{-# DISPLAY Monad.return i = return #-} -- f ∘ return
