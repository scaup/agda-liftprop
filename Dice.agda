module Dice where

open import LiftProp
open import Monad
open import Monad.List
open import Monad2Functor
open import Functor
open import Postulates

-- open import Imports

-- stdlib {{{

open import Function
open import Data.List
open import Data.Nat
open import Data.Product
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- }}}

postulate
  x≤6∧y≤6⇒x+y≤12 : {x y : ℕ} → x ≤ 6 → y ≤ 6 → x + y ≤ 12
  x≤6∧y<x⇒x+y≤11 : {x y : ℕ} → x ≤ 6 → y < x → x + y ≤ 11

-- genericDie {{{

genericDie : List ℕ
genericDie = 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ []

genericDieLP≤6 : LiftProp (λ a → a ≤ 6) genericDie
monadicValueX genericDieLP≤6 = (1 , s≤s z≤n) ∷
                                (2 , s≤s (s≤s z≤n)) ∷
                                (3 , s≤s (s≤s (s≤s z≤n))) ∷
                                (4 , s≤s (s≤s (s≤s (s≤s z≤n)))) ∷
                                (5 , s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) ∷
                                (6 , s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) ∷ []
proofPPE genericDieLP≤6 = refl

-- }}}

-- genericDieTwice {{{

genericDieTwice : List ℕ
genericDieTwice = do
                    x ← genericDie
                    y ← genericDie
                    return (x + y)

genericDieTwiceLP≤12 : LiftProp (λ a → a ≤ 12) genericDieTwice
monadicValueX genericDieTwiceLP≤12 = do
                         (x , px) ← (monadicValueX genericDieLP≤6)
                         (y , py) ← (monadicValueX genericDieLP≤6)
                         return (x + y , x≤6∧y≤6⇒x+y≤12 px py)
proofPPE genericDieTwiceLP≤12 = {!!}

genericDieTwiceLP≤12' : LiftProp (λ a → a ≤ 12) genericDieTwice
genericDieTwiceLP≤12' = let
                          _>>=_ = _>>=LP_
                          return = returnLP
                        in
                        do
                          (x , px) ← genericDieLP≤6
                          (y , py) ← genericDieLP≤6
                          return (x + y , x≤6∧y≤6⇒x+y≤12 px py)

-- }}}

-- someList {{{

postulate
  someList : List ℕ
  someListLP≤6 : LiftProp (λ a → a ≤ 6) someList

-- }}}

-- someListTwice {{{

someListTwice : List ℕ
someListTwice = do
                    x ← someList
                    y ← someList
                    return (x + y)

someListTwiceLP≤12 : LiftProp (λ a → a ≤ 12) someListTwice
someListTwiceLP≤12 = let
                        _>>=_ = _>>=LP_
                        return = returnLP
                      in
                      do
                        (x , px) ← someListLP≤6
                        (y , py) ← someListLP≤6
                        return (x + y , x≤6∧y≤6⇒x+y≤12 px py)

-- }}}

-- someComp {{{

postulate
  M : Set → Set -- some type constructor
  instance
    Mimp : Monad M -- which is actually a monad
  someComp : M ℕ
  someCompLP≤6 : LiftProp (λ a → a ≤ 6) someComp

-- }}}

-- someCompTwice {{{

someCompTwice : M ℕ
someCompTwice = do
                    x ← someComp
                    y ← someComp
                    return (x + y)


someCompTwiceLP≤12 : LiftProp (λ a → a ≤ 12) someCompTwice
someCompTwiceLP≤12 = let
                        _>>=_ = _>>=LP_
                        return = returnLP
                      in
                      do
                        (x , px) ← someCompLP≤6
                        (y , py) ← someCompLP≤6
                        return (x + y , x≤6∧y≤6⇒x+y≤12 px py)

-- }}}

-- someCompSmallerThan {{{

postulate
  someCompSmallerThan : ℕ → M ℕ
  someCompSmallerThaniLP<i : (i : ℕ) → LiftProp (λ a → a < i) (someCompSmallerThan i)

someCompAndSmallerOne : M ℕ
someCompAndSmallerOne = do
                    x ← someComp
                    y ← someCompSmallerThan x
                    return (x + y)


someCompAndSmallerLP≤11 : LiftProp (λ a → a ≤ 11) someCompAndSmallerOne
someCompAndSmallerLP≤11 = let
                            _>>=_ = _>>=LP_
                            return = returnLP
                          in
                          do
                            (x , px) ← someCompLP≤6
                            (y , py) ← (someCompSmallerThaniLP<i x)
                            return (x + y , x≤6∧y<x⇒x+y≤11 px py)

-- }}}

-- veryGeneral {{{

postulate
  X₁ X₂ X₃ X₄ : Set
  P₁ : X₁ → Set
  P₂ : X₂ → Set
  P₃ : X₃ → Set
  P₄ : X₄ → Set

  mx₁ : M X₁
  mx₁LPP₁ : LiftProp P₁ mx₁

  mx₂ : X₁ → M X₂
  mx₂LPP₂ : (x₁ : X₁) → (px₁ : P₁ x₁) → LiftProp P₂ (mx₂ x₁)

  mx₃ : X₁ → X₂ → M X₃
  mx₃LPP₃ : (x₁ : X₁) → (px₁ : P₁ x₁) → (x₂ : X₂) → (px₂ : P₂ x₂) → LiftProp P₃ (mx₃ x₁ x₂)

  mx₄ : X₁ → X₂ → X₃ → M X₄
  mx₄LPP₄ : (x₁ : X₁) → (px₁ : P₁ x₁) → (x₂ : X₂) → (px₂ : P₂ x₂) → (x₃ : X₃) → (px₃ : P₃ x₃) → LiftProp P₄ (mx₄ x₁ x₂ x₃)

something : M X₄
something = do
                 x₁ ← mx₁
                 x₂ ← mx₂ x₁
                 x₃ ← mx₃ x₁ x₂
                 mx₄ x₁ x₂ x₃

somethingLPP₄ : LiftProp P₄ something
somethingLPP₄ = let
                  _>>=_ = _>>=LP_
                  return = returnLP
                in
                do
                  (x₁ , px₁) ← mx₁LPP₁
                  (x₂ , px₂) ← mx₂LPP₂ x₁ px₁
                  (x₃ , px₃) ← mx₃LPP₃ x₁ px₁ x₂ px₂
                  mx₄LPP₄ x₁ px₁ x₂ px₂ x₃ px₃

-- }}}


-- #################################
-- # Proofs without annotated bind #
-- #################################

-- Help Lemma's {{{

helpLemma : {M : Set → Set} {{Mimp : Monad M}} → {A B X : Set} →
  {ma : M A} → {mb : M B} → {p : B → A} → {f : A → M X} → (eq : ma ≡ fmap p mb) →
  ma >>= f ≡ mb >>= (f ∘ p)
helpLemma {M} {{Mimp}} {A} {B} {X} {ma} {mb} {p} {f} eq =
                            begin
                               ma >>= f
                            ≡⟨ cong (λ z → z >>= f) (eq) ⟩
                              fmap p mb >>= f
                            ≡⟨ assoc _ _ mb ⟩
                              mb >>= (λ x → (return (p x) >>= f))
                            ≡⟨ cong (_>>=_ mb) (funext λ x → (leftId _ (p x) ))  ⟩
                              mb >>= (λ x → f (p x))
                            ≡⟨⟩
                              mb >>= (f ∘ p) ∎

helpLemma2 : {M : Set → Set} {{Mimp : Monad M}} →
             {X Y : Set} → {P : Y → Set} → {mx : M X} →
             {f : X → M (Σ[ y ∈ Y ] P y)} →
             fmap proj₁ (mx >>= f) ≡ mx >>= λ x → (fmap proj₁ (f x))
helpLemma2 {M} {{Mimp}} {X} {Y} {P} {mx} {f} = begin fmap proj₁ (mx >>= f) ≡⟨ assoc _ _ _ ⟩ mx >>= (λ x → (fmap proj₁ (f x))) ∎

-- }}}

-- someCompTwice {{{

someCompTwiceLP≤12' : LiftProp (λ a → a ≤ 12) someCompTwice
monadicValueX someCompTwiceLP≤12' = do
                       (x , px) ← (monadicValueX someCompLP≤6)
                       (y , py) ← (monadicValueX someCompLP≤6)
                       return (x + y , x≤6∧y≤6⇒x+y≤12 px py)
proofPPE someCompTwiceLP≤12' =
                       begin
                         (
                         do
                           x ← someComp
                           y ← someComp
                           return (x + y)
                         )
                       ≡⟨ helpLemma (proofPPE someCompLP≤6) ⟩
                         (
                         do
                           (x , px) ← monadicValueX someCompLP≤6
                           y ← someComp
                           return (x + y)
                         )
                       ≡⟨ cong (_>>=_ (monadicValueX someCompLP≤6)) (funext (λ a → helpLemma (proofPPE someCompLP≤6))) ⟩
                         (
                         do
                          (x , px) ← (monadicValueX someCompLP≤6)
                          (y , py) ← (monadicValueX someCompLP≤6)
                          return (x + y)
                         )
                       ≡⟨ cong (_>>=_ (monadicValueX someCompLP≤6)) (funext (λ a → cong (_>>=_ (monadicValueX someCompLP≤6)) (funext λ a₁ →  sym (leftId _ _)))) ⟩
                         (
                         do
                          (x , px) ← (monadicValueX someCompLP≤6)
                          (y , py) ← (monadicValueX someCompLP≤6)
                          fmap proj₁ (return (x + y , x≤6∧y≤6⇒x+y≤12 px py))
                         )
                       ≡⟨ cong (_>>=_ (monadicValueX someCompLP≤6)) (funext (λ a → sym helpLemma2)) ⟩
                         (
                         do
                          (x , px) ← (monadicValueX someCompLP≤6)
                          fmap proj₁
                           do
                           (y , py) ← (monadicValueX someCompLP≤6)
                           (return (x + y , x≤6∧y≤6⇒x+y≤12 px py))
                         )
                       ≡⟨ sym helpLemma2 ⟩
                         (
                         fmap proj₁
                          do
                           (x , px) ← (monadicValueX someCompLP≤6)
                           (y , py) ← (monadicValueX someCompLP≤6)
                           (return (x + y , x≤6∧y≤6⇒x+y≤12 px py))
                         ) ∎

-- }}}

-- someCompAndSmallerOne {{{

someCompAndSmallerLP≤11' : LiftProp (λ a → a ≤ 11) someCompAndSmallerOne
monadicValueX someCompAndSmallerLP≤11' = do
                               (x , px) ← (monadicValueX someCompLP≤6)
                               (y , py) ← (monadicValueX (someCompSmallerThaniLP<i x) )
                               return (x + y , x≤6∧y<x⇒x+y≤11 px py)
proofPPE someCompAndSmallerLP≤11' =
                               begin
                                 (
                                 do
                                   x ← someComp
                                   y ← someCompSmallerThan x
                                   return (x + y)
                                 )
                               ≡⟨ helpLemma (proofPPE someCompLP≤6) ⟩
                                 (
                                 do
                                   (x , px) ← monadicValueX someCompLP≤6
                                   y ← someCompSmallerThan x
                                   return (x + y)
                                 )
                               ≡⟨ cong (_>>=_ (monadicValueX someCompLP≤6)) (funext (λ{(x , px) → helpLemma (proofPPE (someCompSmallerThaniLP<i x))}))  ⟩
                                 (
                                 do
                                   (x , px) ← monadicValueX someCompLP≤6
                                   (y , py) ← monadicValueX (someCompSmallerThaniLP<i x)
                                   return (x + y)
                                 )
                               ≡⟨ cong (_>>=_ (monadicValueX someCompLP≤6)) (funext (λ{(x , px) → cong (_>>=_ (monadicValueX (someCompSmallerThaniLP<i x))) (funext λ{(y , py) → sym (leftId _ _)})})) ⟩
                                 (
                                 do
                                  (x , px) ← (monadicValueX someCompLP≤6)
                                  (y , py) ← (monadicValueX (someCompSmallerThaniLP<i x) )
                                  fmap proj₁ (return (x + y , x≤6∧y<x⇒x+y≤11 px py))
                                 )
                               ≡⟨ cong (_>>=_ (monadicValueX someCompLP≤6)) (funext (λ{(x , px)  → sym helpLemma2}))  ⟩
                                 (
                                 do
                                  (x , px) ← (monadicValueX someCompLP≤6)
                                  fmap proj₁
                                   do
                                    (y , py) ← (monadicValueX (someCompSmallerThaniLP<i x) )
                                    return (x + y , x≤6∧y<x⇒x+y≤11 px py)
                                 )
                               ≡⟨ sym helpLemma2 ⟩
                                 (
                                 fmap proj₁
                                  do
                                   (x , px) ← (monadicValueX someCompLP≤6)
                                   (y , py) ← (monadicValueX (someCompSmallerThaniLP<i x) )
                                   return (x + y , x≤6∧y<x⇒x+y≤11 px py)
                                 ) ∎

-- }}}

-- very general {{{



somethingLPP₄' : LiftProp P₄ something
monadicValueX somethingLPP₄' =
  do
    (x₁ , px₁) ← monadicValueX mx₁LPP₁
    (x₂ , px₂) ← monadicValueX $ mx₂LPP₂ x₁ px₁
    (x₃ , px₃) ← monadicValueX $ mx₃LPP₃ x₁ px₁ x₂ px₂
    monadicValueX $ mx₄LPP₄ x₁ px₁ x₂ px₂ x₃ px₃
proofPPE somethingLPP₄' =
  begin
    (
    do
       x₁ ← mx₁
       x₂ ← mx₂ x₁
       x₃ ← mx₃ x₁ x₂
       mx₄ x₁ x₂ x₃
    )
  ≡⟨ helpLemma (proofPPE mx₁LPP₁) ⟩
    (
    do
       (x₁ , px₁) ← monadicValueX mx₁LPP₁
       x₂ ← mx₂ x₁
       x₃ ← mx₃ x₁ x₂
       mx₄ x₁ x₂ x₃
    )
  ≡⟨ cong (_>>=_ (monadicValueX mx₁LPP₁)) (funext {!!}) ⟩
    (
    do
       (x₁ , px₁) ← monadicValueX mx₁LPP₁
       (x₂ , px₂) ← monadicValueX $ mx₂LPP₂ x₁ px₁
       x₃ ← mx₃ x₁ x₂
       mx₄ x₁ x₂ x₃
    )
  ≡⟨ {!!} ⟩
    (
    do
       (x₁ , px₁) ← monadicValueX mx₁LPP₁
       (x₂ , px₂) ← monadicValueX $ mx₂LPP₂ x₁ px₁
       (x₃ , px₃) ← monadicValueX $ mx₃LPP₃ x₁ px₁ x₂ px₂
       mx₄ x₁ x₂ x₃
    )
  ≡⟨ {!!} ⟩
    (
    do
       (x₁ , px₁) ← monadicValueX mx₁LPP₁
       (x₂ , px₂) ← monadicValueX $ mx₂LPP₂ x₁ px₁
       (x₃ , px₃) ← monadicValueX $ mx₃LPP₃ x₁ px₁ x₂ px₂
       fmap proj₁ (monadicValueX $ mx₄LPP₄ x₁ px₁ x₂ px₂ x₃ px₃)
    )
  ≡⟨ {!!} ⟩
    (
    do
       (x₁ , px₁) ← monadicValueX mx₁LPP₁
       (x₂ , px₂) ← monadicValueX $ mx₂LPP₂ x₁ px₁
       fmap proj₁
         do
           (x₃ , px₃) ← monadicValueX $ mx₃LPP₃ x₁ px₁ x₂ px₂
           monadicValueX $ mx₄LPP₄ x₁ px₁ x₂ px₂ x₃ px₃
    )
  ≡⟨ {!!} ⟩
    (
    do
       (x₁ , px₁) ← monadicValueX mx₁LPP₁
       fmap proj₁
         do
           (x₂ , px₂) ← monadicValueX $ mx₂LPP₂ x₁ px₁
           (x₃ , px₃) ← monadicValueX $ mx₃LPP₃ x₁ px₁ x₂ px₂
           monadicValueX $ mx₄LPP₄ x₁ px₁ x₂ px₂ x₃ px₃
    )
  ≡⟨ {!!} ⟩
    (
    fmap proj₁
      do
        (x₁ , px₁) ← monadicValueX mx₁LPP₁
        (x₂ , px₂) ← monadicValueX $ mx₂LPP₂ x₁ px₁
        (x₃ , px₃) ← monadicValueX $ mx₃LPP₃ x₁ px₁ x₂ px₂
        monadicValueX $ mx₄LPP₄ x₁ px₁ x₂ px₂ x₃ px₃
    ) ∎

-- }}}
