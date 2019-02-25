module Examples.PasswordProofs where

open import MonadTC using (Monad)

open import MonadLift renaming (_>>=L_ to _>>=_; returnL to return)
open import ApplicativeLift renaming (_<*>L_ to _<*>_ ; pureL to pure)
open import FunctorLift
open import Monads.IO
open import Examples.Password

open import Functors.IO
open import Monads.IO
open import Functors.List
open import Monads.List
open import Postulates

open import Data.Nat
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

postulate
  randomL : (n : ℕ) → Lift (λ s → length s ≡ 20) (random n)

if?L_then_else_ : ∀{M A} → {{Mimp : Monad M}} →
  {Q : Predicate A} → {ma₁ ma₂ : M A} →
  {P : Set} → (d : Dec P) →
  (P → Lift Q ma₁) → (¬ P → Lift Q ma₂) →
  Lift Q (if? d then ma₁ else ma₂)
if?L yes p then f else g = f p
if?L no ¬p then f else g = g ¬p

retryL : (n : ℕ) → Lift (λ s → length s ≥ 20) (retry n)
retryL zero = applyL lem (randomL 20)
  where
    lem : {n m : ℕ} → n ≡ m → n ≥ m
    lem {zero} refl = z≤n
    lem {suc n} refl = s≤s (lem refl)
retryL (suc n) = do (s , _) ← nothing2Prove getLine
                    if?L (length s ≥? 20)
                          then (λ p → return (s , p))
                          else (λ _ → retryL n)

choosePasswordLengthy : Lift (λ s → length s ≥ 20) choosePassword
choosePasswordLengthy = retryL 3
