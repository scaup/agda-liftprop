{-# OPTIONS --allow-unsolved-metas #-}

open import Tree
open import Monad.State
open import SCBX
open import Imports

-- ##############################################################
-- # The Hoare State Monad (Wouter Swiersta), slightly adjusted #
-- ##############################################################

record StateDX (S : Set) (A : Set) (P : A → S → S → Set) : Set where
  field
    runStateDX : (s₁ : S) → Σ (A × S) λ{(a , s₂) → P a s₁ s₂}

open StateDX

toDX : ∀{S A} → (k : State S A) → StateDX S A λ a s₁ s₂ → runState k s₁ ≡ (a , s₂)
runStateDX (toDX k) s = runState k s , refl

returnDX : {S A : Set} → (a : A) → StateDX S A λ a' s₁ s₂ → s₁ ≡ s₂ × a' ≡ a
runStateDX (returnDX a) s₁ = (a , s₁) , refl , refl

_>>=DX_ : ∀{A S B} →
          {P₁ : A → S → S → Set} →
          {P₂ : A → B → S → S → Set} →
          StateDX S A P₁ →
          (f : (a : A) → StateDX S B (P₂ a)) →
          StateDX S B λ b s₁ s₃ → Σ[ a ∈ A ] Σ[ s₂ ∈ S ] P₁ a s₁ s₂ × P₂ a b s₂ s₃
runStateDX (k >>=DX f) s₁ with runStateDX k s₁
runStateDX (k >>=DX f) s₁ | (a , s₂) , p₁as₁s₂ with runStateDX (f a) s₂
runStateDX (k >>=DX f) s₁ | (a , s₂) , p₁as₁s₂ | (b , s₃) , p₂abs₂s₃ = (b , s₃) , a , s₂ , p₁as₁s₂ , p₂abs₂s₃

impDX : ∀{S A P Q} → StateDX S A P → (∀{a s₁ s₂} → (P a s₁ s₂) → (Q a s₁ s₂)) → StateDX S A Q
runStateDX (impDX record { runStateDX = k } imp) s₁ = (proj₁ (proj₁ (k s₁)) , proj₂ (proj₁ (k s₁))) , imp (proj₂ (k s₁))

_concluding_ = impDX

-- toggling example {{{

toggleDX : StateDX Bool ⊤ λ a b₁ b₂ → b₁ ≡ b₂
toggleDX = let
              _>>=_ = _>>=DX_
              return = returnDX
            in
            (
            do
              t ← toDX (modify not)
              -- ⟦ b₂ ⟧
              t' ← toDX (modify not)
              -- ⟦ b₃ ⟧
              (return tt)
            )

            concluding

            λ{ (t , b₂ , refl , t' , b₃ , refl , refl , refl) → triv}
              where
                triv : {b : Bool} → b ≡ not (not b)
                triv {false} = refl
                triv {true} = refl

-- }}}

-- easyExample {{{

easyExample : StateDX ℕ ℕ λ a n₁ n₂ → n₂ ≡ 5
easyExample = let
         _>>=_ = _>>=DX_
         return = returnDX
       in
       (
       do
         t ← (toDX (put 5))
         -- ⟦ n₂ ⟧
         m ← toDX get
         -- ⟦ n₃ ⟧
         return m
       )

       concluding

       λ{ (t , n₂ , refl , m , n₃ , refl , refl , refl) → refl}

-- }}}

-- easyExample2 {{{

easyExample2 : StateDX ℕ ℕ λ a s₁ s₂ → a ≡ 0
easyExample2 = let
                _>>=_ = _>>=DX_
                return = returnDX
              in
              (
              do
                n ← (toDX get)
                -- ⟦ n₂ ⟧
                t₁ ← (toDX (modify double))
                -- ⟦ n₃ ⟧
                t₂ ← (toDX (modify double))
                -- ⟦ n₄ ⟧
                m ← (toDX get)
                -- ⟦ n₅ ⟧
                return (m - n - n - n - n)
              )

              concluding

              λ{ (n , n₂ , refl , t₁ , n₃ , refl , t₂ , n₄ , refl , m , n₅ , refl , refl , refl) → triv {n}}
                where
                  _-_ : ℕ → ℕ → ℕ
                  m - zero = m
                  zero - suc n = zero
                  suc m - suc n = m - n
                  infixr 3 _-_

                  double : ℕ → ℕ
                  double zero = zero
                  double (suc x) = suc (suc (double x))

                  postulate
                    triv : {x : ℕ} → (double (double x) - x - x - x - x) ≡ 0

-- }}}

-- easyExample3 (not expressible) {{{

postulate
  smallestNonEmpty : Σ[ xs ∈ List ℕ ] xs ≢ [] → ℕ

easyExample3 : StateDX (List ℕ) (List ℕ) {!!}
easyExample3 = let
                _>>=_ = _>>=DX_
                return = returnDX
              in
              (
              do
                t₁ ← (toDX (modify (_∷_ 6)))
                -- ⟦ as₂ ⟧
                xs ← (toDX get)
                -- ⟦ as₃ ⟧
                t₂ ← (toDX (modify (_∷_ (smallestNonEmpty {!!}))))
                -- ⟦ as₄ ⟧
                (toDX get)
              )

              concluding

              {!!}
              -- λ{ (n , n₂ , refl , t₁ , n₃ , refl , t₂ , n₄ , refl , m , n₅ , refl , refl , refl) → triv {n}}

-- }}}

-- tree relabelling {{{

labelDX : {A : Set} → (t : Tree A) → StateDX ℕ (Tree ℕ) Proof
labelDX (leaf a) = let
                     _>>=_ = _>>=DX_
                     return = returnDX
                   in
                     (
                     do
                       n ← toDX (fresh)
                       -- ⟦ s₂ ⟧
                       (return (leaf n))
                     )
                     concluding
                     (λ{(n , s₂ , refl , refl , refl) →  record { n₂NotZero = sucn≠0
                                                                ; initial≤final = n≤sucn
                                                                ; proofLower = leafBound n≤n
                                                                ; proofUpper = leafBound n≤n
                                                                ; proofNoDups = refl
                                                                } })
labelDX (node l r) = let
                        _>>=_ = _>>=DX_
                        return = returnDX
                      in
                      (
                      do
                        -- ⟦ s₁ ⟧
                        l' ← labelDX l -- → pl'
                        -- ⟦ s₂ ⟧
                        r' ← labelDX r -- → pr'
                        -- ⟦ s₃ ⟧
                        return (node l' r')
                      )

                      concluding

                      λ{ (l' , s₂ , pl' , r' , s₃ , pr' , refl , refl) → record { n₂NotZero = n₂NotZero pr'
                                                                                ; initial≤final = transitivity (initial≤final pl') (initial≤final pr')
                                                                                ; proofLower = leftAndRightBound
                                                                                                   (proofLower pl')
                                                                                                   (llbt (initial≤final pl') (proofLower pr'))
                                                                                ; proofUpper = leftAndRightBound
                                                                                                   (uubt (n≤m=>pn≤pm (initial≤final pr')) (proofUpper pl'))
                                                                                                   (proofUpper pr')
                                                                                ; proofNoDups = meatOfIt (n₂NotZero pl') (proofUpper pl')
                                                                                                   (proofLower pr') (proofNoDups pl') (proofNoDups pr')
                                                                                }}

-- }}}

-- suggestion to specialize LiftProp to state with hoare state {{{

forgetDX : ∀{S A P} → StateDX S A P → State S A
runState (forgetDX record { runStateDX = k }) s = proj₁ (k s)

-- manually

forgetDXlabelDX≡label : {A : Set} → (t : Tree A) → (label t) ≡ forgetDX (labelDX t)
forgetDXlabelDX≡label (leaf a) = refl
forgetDXlabelDX≡label (node l r) with forgetDXlabelDX≡label l | forgetDXlabelDX≡label r
forgetDXlabelDX≡label (node l r) | e1 | e2 =
  begin
    label (node l r)
  ≡⟨ {!!} ⟩
    forgetDX (labelDX (node l r)) ∎


record LiftPropStateD {A S : Set} (P : A → S → S → Set) (stateComputation : State S A) : Set where
  constructor _,_
  field
    stateComputationDX : StateDX S A P
    proofPPE : stateComputation ≡ forgetDX stateComputationDX

labelLPUniqueLabels : {A : Set} → (t : Tree A) → LiftPropStateD Proof (label t)
labelLPUniqueLabels t = labelDX t , forgetDXlabelDX≡label t

_>>=LPDS_ : {!!}
_>>=LPDS_ = {!!}

-- }}}
