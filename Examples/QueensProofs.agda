module Examples.QueensProofs where

open import Examples.Queens
open import FunctorTC
open import FunctorLift
open import MonadLift renaming (returnL to return ; _>>=L_ to _>>=_)
open import Monads.List
open import Functors.List

open import Examples.ListFunctionsProofs

-- stdlib {{{

open import Data.Nat
-- open import Data.Integer renaming (_-_ to _-ℤ_ ; _⊖_ to _-_ ; _+_ to _+ℤ_ ; _<_ to _<ℤ_)
open import Data.List hiding (filter)
open import Data.Bool hiding (_≟_)
open import Data.Product hiding (zip)
open import Data.Unit hiding (_≟_; _≤?_; _≤_)
open import Data.Empty
open import Data.Sum
open import Function

open import Relation.Unary using (Decidable)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding ([_])

-- }}}

UptoBound : (n : ℕ) → Lift (λ x → x < n) (upto n)
UptoBound zero = []L
UptoBound (suc n) = applyL s≤s (rangeUpBound 0 n)


queensFit : (n : ℕ) → (k : ℕ) → Lift (Lift λ q → q < n) (queens n k)
queensFit n zero = return ([] , []L)
queensFit n (suc k) =
  do
    (qs , qsFit) ← queensFit n k
    (q , qFit) ← filterPreserves (λ q → qs areNotAttacking q) (UptoBound n)
    return (qs ++ [ q ] , (qsFit ++L [ qFit ]L))

-- helper functions {{{

_∈_ : {A : Set} → A → List A → Set
a ∈ [] = ⊥
a ∈ (x ∷ xs) = a ≡ x ⊎ (a ∈ xs)

_∉_ : {A : Set} → A → List A → Set
a ∉ xs = ¬ a ∈ xs

NoDup : {A : Set} → List A → Set
NoDup [] = ⊤
NoDup (x ∷ xs) = x ∉ xs × NoDup xs

-- }}}

ArePeaceful : List ℕ → Set
ArePeaceful qs
  = NoDup (fmap upwardDiagonal coordinates)
  × NoDup (fmap downwardDiagonal coordinates)
  × NoDup (fmap row coordinates)
    where
      coordinates = toCoordinates qs

bookkeeping : (qs : List ℕ) → (q : ℕ) →
  ArePeaceful qs → (qs areNotAttacking q ≡ true) →
  ArePeaceful (qs ++ [ q ])
bookkeeping qs q qsP b = {!!}
                       , {!!}
                       , {!!}

queensPeaceful : (n : ℕ) → (k : ℕ) → Lift ArePeaceful (queens n k)
queensPeaceful n zero = return ([] , (tt , tt , tt))
queensPeaceful n (suc k) =
  do
    (qs , qsPeaceful) ← queensPeaceful n k
    (q , qs¬Attackingq) ← filterNew ((λ q → qs areNotAttacking q)) (upto n)
    return ((qs ++ [ q ]) , bookkeeping qs q qsPeaceful qs¬Attackingq )

queensAll : (n : ℕ) → (k : ℕ) → Lift _ (queens n k)
queensAll n k = (queensPeaceful n k) ,L (queensFit n k)
