open import Relation.Binary.PropositionalEquality

postulate
  funext : ∀{ℓA ℓB} {A : Set ℓA} {B : A → Set ℓB} {f g : (a : A) → B a} → ((a : A) → f a ≡ g a) → f ≡ g
