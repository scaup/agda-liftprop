module Examples.DiceProofsManual where

open import Examples.Dice

open import Monads.IO
open import Functors.IO
open import Functors.List
open import Monads.List
open import Lift
open import MonadTC
open import Postulates

-- stdlib {{{

open import Data.List
open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Function
open ≡-Reasoning

-- }}}

postulate
  sumBound6IsBound12 : {x y : ℕ} → x ≤ 6 → y ≤ 6 → x + y ≤ 12

  genericDieBound6 : Lift (λ x → x ≤ 6) genericDie

aWitness : IO (Σ ℕ λ x → x ≤ 12)
aWitness = do
             (x , px) ← witness genericDieBound6
             (y , py) ← witness genericDieBound6
             return (x + y , sumBound6IsBound12 px py)

_↔_ = trans
infixl 4 _↔_

cumbersomeProof : twoDice ≡ fmap proj₁ aWitness
cumbersomeProof =
  begin
    (do x ← genericDie
        y ← genericDie
        return (x + y))
  ≡⟨ cong (flip _>>=_ _) (corresponds genericDieBound6) ⟩
    (do x ← fmap proj₁ (witness genericDieBound6)
        y ← genericDie
        return (x + y))
  ≡⟨ fmap->>= _ _ _ ⟩
    (do (x , px) ← witness genericDieBound6
        y ← genericDie
        return (x + y))
  ≡⟨ cong (_>>=_ (witness genericDieBound6)) (funext λ _ → cong (flip _>>=_ _) (corresponds genericDieBound6)) ⟩
    (do (x , px) ← witness genericDieBound6
        y ← fmap proj₁ (witness genericDieBound6)
        return (x + y))
  ≡⟨ cong (_>>=_ _) (funext λ _ → fmap->>= _ _ _) ⟩
    (do (x , px) ← witness genericDieBound6
        (y , py) ← witness genericDieBound6
        return (x + y))
  ≡⟨ cong (_>>=_ _) (funext λ a → cong (_>>=_ _) (funext λ _ → sym (fmap-return proj₁ _))) ⟩
    (do (x , px) ← witness genericDieBound6
        (y , py) ← witness genericDieBound6
        fmap (proj₁ {B = λ n → n ≤ 12}) (return (x + y , sumBound6IsBound12 px py)))
  ≡⟨ cong (_>>=_ _) (funext λ _ → sym (fmap-move->>= _ _ _ )) ⟩
    (do (x , px) ← witness genericDieBound6
        fmap (proj₁ {B = λ n → n ≤ 12})
          do (y , py) ← witness genericDieBound6
             return (x + y , sumBound6IsBound12 px py))
  ≡⟨ sym (fmap-move->>= _ _ _) ⟩
    fmap proj₁ (do (x , px) ← witness genericDieBound6
                   (y , py) ← witness genericDieBound6
                   return (x + y , sumBound6IsBound12 px py)) ∎
