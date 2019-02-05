module Examples.PasswordProofs where

open import Examples.Password

open import MonadTC renaming (_>>=_ to _>>=M_; return to returnM)
open import Functors.IO
open import Monads.IO
open import Functors.List
open import Monads.List
open import Lift
open import Lift.MonadTC renaming (_>>=L_ to _>>=_; returnL to return)
open import Postulates

-- stdlib {{{

open import Data.List hiding (length)
open import Data.Nat
open import Data.Product
open import Data.Unit hiding (_≤?_)
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable
open import Relation.Nullary

-- }}}

postulate
  randomL : (n : ℕ) → Lift (λ s → length s ≡ 20) (random n)

retryL : (n : ℕ) → Lift (λ s → length s ≥ 20) (retry n)
retryL zero = implicationL (λ a x → {!!}) (randomL 20)
retryL (suc n) = do (s , _) ← nothing2Prove getLine
                    if?L (length s ≥? 20)
                          then (λ p → return (s , p))
                          else (λ _ → retryL n)

choosePasswordLengthy : Lift (λ s → length s ≥ 20) choosePassword
choosePasswordLengthy = retryL 3

{-
retryL : (n : ℕ) → Lift (λ s → length s ≥ 20) (retry n)
retryL zero = implicationL (λ a x → {!!}) (randomL 20)
retryL (suc n) = do (s , _) ← nothing2Prove getLine
                    caseL_of_  {α} (length s ≥? 20)
                          λ{ (yes p) → return {!s , p!} ;
                             (no ¬p) → retryL n}

-}
