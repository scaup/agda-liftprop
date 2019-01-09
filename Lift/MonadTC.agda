{-# OPTIONS --allow-unsolved-metas #-}

module Lift.MonadTC where

open import Lift
open import MonadTC

open import Postulates

-- stdlib {{{

open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- }}}

returnL : {M : Set → Set} → {{ Mimp : Monad M }} →
           {A : Set} → {P : A → Set} →
           (aX : Σ A P) → Lift {A} {M} P (return (proj₁ aX))
witness (returnL (a , p)) = return (a , p)
corresponds (returnL (a , p)) = sym $
  begin
    fmap proj₁ (return (a , p))
  ≡⟨ compatiblefmap ⟩
    return (a , p) >>= (return ∘ proj₁)
  ≡⟨ leftId _ _ ⟩
    return a ∎

_>>=L_ : {M : Set → Set} → {{ Mimp : Monad M }} →
         {A B : Set} → {P : A → Set} → {Q : B → Set} →
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

_>>L_ : {M : Set → Set} → {{ Mimp : Monad M }} →
        {A B : Set} → {P : A → Set} → {Q : B → Set} →
        {ma : M A} → {mb : M B} →
        Lift P ma → Lift Q mb → Lift Q (ma >> mb)
_>>L_ p↑Pma p↑[b←mb]Qb = p↑Pma >>=L λ _ → p↑[b←mb]Qb


_>>=R_ : ∀{M A B P} → {{Mimp : Monad M}} → {ma : M A} →
  (Lift P ma) →
  (Σ A P → M B) →
  M B
maLP >>=R fᵣ = witness maLP >>= fᵣ

BindRValid : ∀{M A B P} → {{Mimp : Monad M}} → (ma : M A) →
  (Pma : Lift P ma) →
  (fᵣ : Σ A P → M B) →
  (f : A → M B) →
  (Res f P ≡ fᵣ) →
  Pma >>=R fᵣ ≡ ma >>= f
BindRValid ma Pma fᵣ f proofR = sym $
  begin
    ma >>= f
  ≡⟨ cong (flip _>>=_ f) (corresponds Pma) ⟩
    fmap proj₁ (witness Pma) >>= f
  ≡⟨ fmap->>= _ _ _ ⟩
    (witness Pma) >>= (f ∘ proj₁)
  ≡⟨ cong (_>>=_ (witness Pma)) proofR ⟩
    (witness Pma) >>= fᵣ ∎
