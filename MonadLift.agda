open import MonadTC

module MonadLift {M : Set → Set} {{mImp : Monad M}} where

open import ApplicativeLift {M} public
open import FunctorLift {M}
open import Relation.Binary.PropositionalEquality

open import Postulates

returnL : {A : Set} → {P : Predicate A} →
          (aX : Σ A P) → Lift P (return (proj₁ aX))
returnL (_ , p) = pureL p

_>>=L_ : {A B : Set} → {P : A → Set} → {Q : B → Set} →
          {ma : M A} → {f : A → M B} →
            Lift P ma →
            ((aX : Σ A P) → Lift Q (f (proj₁ aX))) →
            Lift Q (ma >>= f)
witness (maP >>=L f) = witness maP >>= (witness ∘ f)
corresponds (_>>=L_ {ma = ma} {f = f} maP fPQ) =
                  begin
                    ma >>= f
                  ≡⟨ cong (flip _>>=_ f) (corresponds maP) ⟩
                    (do x <- fmap proj₁ (witness maP)
                        f x)
                  ≡⟨ fmap->>= f proj₁ (witness maP) ⟩
                    (do x ← (witness maP)
                        f (proj₁ x))
                  ≡⟨ cong (_>>=_ (witness maP)) (funext (corresponds ∘ fPQ)) ⟩
                    (do y ← (witness maP)
                        fmap proj₁ (witness (fPQ y)))
                  ≡⟨ cong (_>>=_ (witness maP)) (funext (λ a → compatiblefmap)) ⟩
                    (do y ← (witness maP)
                        (witness (fPQ y) >>= (return ∘ proj₁)))
                  ≡⟨ sym $ assoc _ _ _ ⟩
                    (do y ← (witness maP)
                        witness (fPQ y)) >>= (return ∘ proj₁)
                  ≡⟨ sym compatiblefmap ⟩
                    fmap proj₁ (do y ← (witness maP)
                                   witness (fPQ y)) ∎

_>>L_ : {A B : Set} → {P : A → Set} → {Q : B → Set} →
        {ma : M A} → {mb : M B} →
        Lift P ma → Lift Q mb → Lift Q (ma >> mb)
_>>L_ p↑Pma p↑[b←mb]Qb = p↑Pma >>=L λ _ → p↑[b←mb]Qb

_>>=R_ : ∀{A B P} → {ma : M A} →
  (Lift P ma) →
  (Σ A P → M B) →
  M B
maLP >>=R fᵣ = witness maLP >>= fᵣ

bindRValid : ∀{A B P} → (ma : M A) →
  (Pma : Lift P ma) →
  (fᵣ : Σ A P → M B) →
  (f : A → M B) →
  (Res P f ≡ fᵣ) →
  Pma >>=R fᵣ ≡ ma >>= f
bindRValid ma Pma fᵣ f proofR = sym $
  begin
    ma >>= f
  ≡⟨ cong (flip _>>=_ f) (corresponds Pma) ⟩
    fmap proj₁ (witness Pma) >>= f
  ≡⟨ fmap->>= _ _ _ ⟩
    (witness Pma) >>= (f ∘ proj₁)
  ≡⟨ cong (_>>=_ (witness Pma)) proofR ⟩
    (witness Pma) >>= fᵣ ∎
