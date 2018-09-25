open import Function public
open import Relation.Binary.PropositionalEquality public hiding ([_])
open ≡-Reasoning public
open import Data.Empty public
open import Data.Product public hiding (map ; zip)
open import Data.List public
open import Data.Bool public hiding (_≟_ ; decSetoid)
open import Data.Unit public hiding (_≟_ ; decSetoid ; preorder ; setoid ; _≤_ ; _≤?_)
open import Data.Nat public
open import Data.Maybe public hiding (decSetoid ; setoid ; map)
open import Relation.Nullary public

postulate
  funext : ∀{ℓA ℓB} {A : Set ℓA} {B : A → Set ℓB} {f g : (a : A) → B a} → ((a : A) → f a ≡ g a) → f ≡ g
