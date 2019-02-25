module Examples.QueensProofs where

open import Examples.ListFunctions
open import Examples.Queens
open import Examples.ListFunctionsProofs
open import Prelude
open Prelude.Integers
open Prelude.Booleans

open import FunctorTC
open import FunctorLift
open import MonadLift renaming (returnL to return ; _>>=L_ to _>>=_)
open import Monads.List
open import Functors.List

open import Data.List hiding (filter)
open import Data.Product hiding (zip)
open import Relation.Binary.PropositionalEquality hiding ([_])

Fitting : (n : ℕ) → Predicate QConfig
Fitting n = Lift (λ q → q ≤ pred n)

queenConfigsFit : (n : ℕ) → (k : ℕ) → Lift (Fitting n) (queenConfigs n k)
queenConfigsFit n zero = return ([] , []L)
queenConfigsFit n (suc k) =
  do
    (qs , qsFit) ← queenConfigsFit n k
    (q , qFit) ← filterPreserves (λ q → qs areNotAttacking q) (rangeUpBound 0 (pred n))
    return (qs ++ [ q ] , (qsFit ++L [ qFit ]L))

NoDup : {A : Set} → List A → Set
NoDup [] = ⊤
NoDup (x ∷ xs) = {!!} --  x ∉ xs × NoDup xs

Peaceful : List ℕ → Set
Peaceful qs
  = NoDup (fmap upwardDiagonal coordinates)
  × NoDup (fmap downwardDiagonal coordinates)
  × NoDup (fmap row coordinates)
    where
      coordinates = toCoordinates qs

addPeaceFully : (qs : List ℕ) → (q : ℕ) →
  Peaceful qs → (qs areNotAttacking q ≡ true) →
  Peaceful (qs ++ [ q ])
addPeaceFully qs q qsP b = {!!}
                         , {!!}
                         , {!!}

queenConfigsPeaceful : (n : ℕ) → (k : ℕ) → Lift Peaceful (queenConfigs n k)
queenConfigsPeaceful n zero = return ([] , (tt , tt , tt))
queenConfigsPeaceful n (suc k) =
  do
    (qs , qsPeaceful) ← queenConfigsPeaceful n k
    (q , qs¬Attackingq) ← filterNew ((λ q → qs areNotAttacking q)) (range 0 (pred n))
    return ((qs ++ [ q ]) , addPeaceFully qs q qsPeaceful qs¬Attackingq )

Valid : ℕ → Predicate QConfig
Valid n = Fitting n ∧ Peaceful

queenConfigsValid : (n : ℕ) → (k : ℕ) → Lift (Valid n) (queenConfigs n k)
queenConfigsValid n k = queenConfigsFit n k ,L queenConfigsPeaceful n k
