module MonadLPAnd where
-- open import Imports

open import Postulates
open import Monad
open import LiftProp
open import Monad2Functor
open import Functor

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

record MonadLPAnd (M : Set → Set) {{Mimp : Monad M}} : Set₁ where
  field
    -- monad : Monad M
    _∧LP_ : {A : Set} → {ma : M A} → {P Q : Predicate A} →
            LiftProp P ma → LiftProp Q ma → LiftProp (P ∧ Q) ma

open MonadLPAnd {{...}} public

open import Monad.List

instance
  listlpand : MonadLPAnd List
  listlpand = record { _∧LP_ = _∧LPlist_ }
    where
      _∧LPlist_ : {A : Set} → {as : List A} → {P Q : Predicate A} →
                  LiftProp P as → LiftProp Q as → LiftProp (P ∧ Q) as
      _∧LPlist_ {as = []} lpP lpQ = ⟦ [] <> refl ⟧
      _∧LPlist_ {as = x ∷ as} ⟦ [] <> () ⟧ lpQ
      _∧LPlist_ {as = x ∷ as} ⟦ x₁ ∷ a <> proofPPE₁ ⟧ ⟦ [] <> () ⟧
      _∧LPlist_ {as = x ∷ as} ⟦ x₁ ∷ a <> proofPPE₁ ⟧ ⟦ x₂ ∷ c <> proofPPE₂ ⟧ with α proofPPE₁ | α proofPPE₂
        where
          α : {A : Set} → {xs ys : List A} → {x y : A} → x ∷ xs ≡ y ∷ ys → x ≡ y × xs ≡ ys
          α refl = refl , refl
      _∧LPlist_ {_} {x ∷ as} ⟦ (.x , px) ∷ xps <> proofPPE₁ ⟧ ⟦ (.x , qx) ∷ xqs <> proofPPE₂ ⟧ | refl , snd | refl , snd₁ = (x , px , qx) ∷LP (⟦ xps <> snd ⟧ ∧LPlist ⟦ xqs <> snd₁ ⟧)
        where
          _∷LP_ : {A : Set} → {P : Predicate A} → {xs : List A} →
                  (ap : Σ A P) → LiftProp P xs → LiftProp P (proj₁ ap ∷ xs)
          ap ∷LP ⟦ xsX <> proofPPE₁ ⟧ = ⟦ ap ∷ xsX <> cong (_∷_ (proj₁ ap)) proofPPE₁ ⟧
