module ExperimentsWithImplicits where

open import LiftProp
open import Monad
open import Monad2Functor
open import Functor
open import Data.Product

open import Function

postulate
  M : Set → Set
  instance
    Mimp : Monad M
  X₁ X₂ X₃ X₄ X₅ : Set

  mx₁ : M X₁
  mx₂ : X₁ → M X₂
  mx₃ : X₁ → M X₃
  mx₄ : X₁ → X₃ → M X₄
  mx₅ : X₁ → X₃ → X₄ → M X₅

  P₁ : Predicate X₁
  P₂ : Predicate X₂
  P₃ : Predicate X₃
  P₄ : Predicate X₄
  P₅ : Predicate X₅

  lp₁ : LiftProp P₁ mx₁
  lp₂ : (x₁ : Σ X₁ P₁) → LiftProp P₂ (mx₂ (proj₁ x₁))
  lp₃ : (x₁ : Σ X₁ P₁) → LiftProp P₃ (mx₃ (proj₁ x₁))
  lp₄ : (x₁ : Σ X₁ P₁) → (x₃ : Σ X₃ P₃) →
        LiftProp P₄ (mx₄ (proj₁ x₁) (proj₁ x₃))
  lp₅ : (x₁ : Σ X₁ P₁) → (x₃ : Σ X₃ P₃) → (x₄ : Σ X₄ P₄) →
        LiftProp P₅ (mx₅ (proj₁ x₁) (proj₁ x₃) (proj₁ x₄))

mx : M X₅
mx =
  do
    x₁p ← mx₁
    mx₂ x₁p
    x₃p ← mx₃ x₁p
    x₄p ← mx₄ x₁p x₃p
    mx₅ x₁p x₃p x₄p

postulate
  lp₁' : LiftProp P₁ mx₁
  -- lp₂' : no claim
  lp₃' : (x₁ : Σ X₁ P₁) → LiftProp P₃ (mx₃ (proj₁ x₁))
  -- lp₄' : no claim
  lp₅' : (x₁ : Σ X₁ P₁) → (x₃ : Σ X₃ P₃) → (x₄ : X₄) →
         LiftProp P₅ (mx₅ (proj₁ x₁) (proj₁ x₃) x₄)

lp' : LiftProp P₅ mx
lp' =
  let
    _>>=_ = _>>=LP'_
    _>>_ = _>>LP'_
    return = returnLP'
  in
  do
    p₁ ← lp₁'
    noClaim
    p₃ ← lp₃' (_ , p₁)
    noClaim
    lp₅' (_ , p₁) (_ , p₃) (_)


-- simple toy example

open import Monad.List
open import Data.List
open import Data.Nat
open import LiftProp.List

-- stdlib {{{

open import Relation.Binary.PropositionalEquality

-- }}}

repeat : ℕ → ℕ → List ℕ
repeat zero m = []
repeat (suc n) m = m ∷ repeat n m

repeatLP : {n m : ℕ} → {P : Predicate ℕ} → (p : P m) → LiftProp P (repeat n m)
repeatLP {zero} {m} {P} p = ⟦ [] <> refl ⟧
repeatLP {suc n} {m} {P} p = (m , p) ∷LP repeatLP {n} {m} {P} p

data IsEven : ℕ → Set where
  zeroEven : IsEven 0
  nsucsucEven : {n : ℕ} → IsEven n → IsEven (suc (suc n))

even8 : IsEven 8
even8 = nsucsucEven (nsucsucEven (nsucsucEven (nsucsucEven zeroEven)))

repetitionsConcrete : List ℕ
repetitionsConcrete = 1 ∷ 2 ∷ 3 ∷ []

sillyConcrete : List ℕ
sillyConcrete = repetitionsConcrete >>= λ r → (repeat r 8)

postulate
  repetitionsAbstract : List ℕ

sillyAbstract : List ℕ
sillyAbstract = repetitionsAbstract >>= λ r → (repeat r 8)

sillyAbstractProof : Lift IsEven sillyAbstract
sillyAbstractProof = noClaim {fa = repetitionsAbstract} >>LP' repeatLP (even8)

sillyConcreteProof : Lift IsEven sillyConcrete
sillyConcreteProof = noClaim {fa = repetitionsConcrete} >>LP' λ {a} → repeatLP {a} even8

--sillyConcreteProofObviouslywrong : Lift IsEven sillyConcrete
--sillyConcreteProofObviouslywrong = noClaim {fa = 9 ∷ []} >>LP' λ {a} → repeatLP {a} even8

-----

data MonadSyntax (M : Set → Set) {{mM : Monad M}} : (A : Set) → Set₁ where
  [return] : ∀ {A} → A → MonadSyntax M A
  _[>>=]_ : ∀ {A B} → MonadSyntax M A → (A → MonadSyntax M B) → MonadSyntax M B
  wrap[_] : ∀ {A} → M A → MonadSyntax M A

data LPSyntax {M : Set → Set} {{mM : Monad M}} : {A : Set} (P : A → Set) → MonadSyntax M A → Set₁ where
  [returnLP] : ∀{A P} {a : A} → P a → LPSyntax P ([return] a)
  _[>>=LP]_ : ∀{A B P Q} {ma : MonadSyntax M A} (pma : LPSyntax P ma)
              {f : A → MonadSyntax M B} (pf : {a : A} → P a → LPSyntax Q (f a))
              → LPSyntax Q (ma [>>=] f)
  wrapLP[_] : ∀{A P} {ma : M A} → Lift P ma → LPSyntax P wrap[ ma ]

digest : ∀{M} {A} → {{mM : Monad M}} → MonadSyntax M A → M A
digest ([return] x) = return x
digest (ma [>>=] f) = digest ma >>= (digest ∘ f)
digest wrap[ ma ] = ma

digestLP : ∀{M A P} → {{mM : Monad M}} → {ma : MonadSyntax M A} → LPSyntax P ma → Lift P (digest ma)
digestLP ([returnLP] pa) = returnLP (_ , pa)
digestLP (pma [>>=LP] pf) = digestLP pma >>=LP λ {(a , pa) → digestLP (pf pa)}
digestLP wrapLP[ pma ] = pma

[sillyConcrete] : MonadSyntax List ℕ
[sillyConcrete] = wrap[ repetitionsConcrete ] [>>=] λ r → wrap[ repeat r 8 ]

[sillyConcreteProof] : LPSyntax IsEven [sillyConcrete]
[sillyConcreteProof] = wrapLP[ noClaim ] [>>=LP] λ _ → wrapLP[ repeatLP even8 ]

sillyConcreteProof' : Lift IsEven sillyConcrete
sillyConcreteProof' = digestLP [sillyConcreteProof]
