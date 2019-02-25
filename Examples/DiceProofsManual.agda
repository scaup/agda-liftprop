module Examples.DiceProofsManual where

open import Examples.Dice

open import Monads.IO
open import Functors.IO
open import Monads.List
open import FunctorLift
open import MonadTC
open import FunctorTC
open import Postulates

open import Data.List
open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Function
open ≡-Reasoning

open import Examples.Dice
open WithMonad using (twoDice)

open import Examples.DiceProofs using (sumOfBound6IsBound12 ; dieBound6)

aWitness : IO (Σ ℕ λ x → x ≤ 12)
aWitness = do
             (x , px) ← witness dieBound6
             (y , py) ← witness dieBound6
             return (x + y , sumOfBound6IsBound12 px py)

cumbersomeProof : twoDice ≡ fmap proj₁ aWitness
cumbersomeProof =
  begin
    (do x ← die
        y ← die
        return (x + y))
  ≡⟨ cong (flip _>>=_ _) (corresponds dieBound6) ⟩
    (do x ← fmap proj₁ (witness dieBound6)
        y ← die
        return (x + y))
  ≡⟨ fmap->>= _ _ _ ⟩
    (do (x , px) ← witness dieBound6
        y ← die
        return (x + y))
  ≡⟨ cong (_>>=_ (witness dieBound6)) (funext λ _ → cong (flip _>>=_ _) (corresponds dieBound6)) ⟩
    (do (x , px) ← witness dieBound6
        y ← fmap proj₁ (witness dieBound6)
        return (x + y))
  ≡⟨ cong (_>>=_ _) (funext λ _ → fmap->>= _ _ _) ⟩
    (do (x , px) ← witness dieBound6
        (y , py) ← witness dieBound6
        return (x + y))
  ≡⟨ cong (_>>=_ _) (funext λ a → cong (_>>=_ _) (funext λ _ → sym (fmap-return proj₁ _))) ⟩
    (do (x , px) ← witness dieBound6
        (y , py) ← witness dieBound6
        fmap (proj₁ {B = λ n → n ≤ 12}) (return (x + y , sumOfBound6IsBound12 px py)))
  ≡⟨ cong (_>>=_ _) (funext λ _ → sym (fmap-move->>= _ _ _ )) ⟩
    (do (x , px) ← witness dieBound6
        fmap (proj₁ {B = λ n → n ≤ 12})
          do (y , py) ← witness dieBound6
             return (x + y , sumOfBound6IsBound12 px py))
  ≡⟨ sym (fmap-move->>= _ _ _) ⟩
    fmap proj₁ (do (x , px) ← witness dieBound6
                   (y , py) ← witness dieBound6
                   return (x + y , sumOfBound6IsBound12 px py)) ∎
