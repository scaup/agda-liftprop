module Queens where

open import Monad.List
open import Monad
open import LiftProp
open import LiftProp.List


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

-- }}}


-- helper functions {{{

p₁ = proj₁
p₂ = proj₂

_∈_ : {A : Set} → A → List A → Set
a ∈ [] = ⊥
a ∈ (x ∷ xs) = a ≡ x ⊎ (a ∈ xs)

_∈?_ : (a : ℕ) → (xs : List ℕ) → Dec (a ∈ xs)
a ∈? [] = no id
a ∈? (x ∷ xs) with a ≟ x
(a ∈? (x ∷ xs)) | yes p = yes (inj₁ p)
(a ∈? (x ∷ xs)) | no ¬p with a ∈? xs
(a ∈? (x ∷ xs)) | no ¬p | yes p = yes (inj₂ p)
(a ∈? (x ∷ xs)) | no ¬p | no ¬p₁ = no {!!}

decNegProp : (P : Set) → Dec P → Dec (¬ P)
decNegProp P (yes p) = no λ z → z p
decNegProp P (no ¬p) = yes ¬p

_∉_ : {A : Set} → A → List A → Set
a ∉ xs = ¬ (a ∈ xs)

_∉?_ : (a : ℕ) → (xs : List ℕ) → Dec (a ∉ xs)
_∉?_ a xs = decNegProp (a ∈ xs) (a ∈? xs)

addX : List ℕ → List (ℕ × ℕ)
addX xs = f 0 (reverse xs)
  where
    f : ℕ → List ℕ → List (ℕ × ℕ)
    f n [] = []
    f n (x ∷ xs) = (n , x) ∷ f (suc n) xs

_-_ : ℕ → ℕ → ℕ
x - zero = x
zero - suc y = zero
suc x - suc y = x - y

-- }}}

NoDup : List ℕ → Set
NoDup [] = ⊤
NoDup (x ∷ xs) = x ∉ xs × NoDup xs


PeacefulQueens : ℕ → List ℕ → Set
PeacefulQueens n qs
  = LiftProp (\q → q < n) qs
  × NoDup (fmap ((λ{ (x , y) → x + y })) (addX qs))
  × NoDup (fmap ((λ{ (x , y) → (x + n) - y })) (addX qs))


_[_]AreNotAttacking_ : List ℕ → ℕ → ℕ → Set
qs [ n ]AreNotAttacking q
  = q ∉ qs
  × (q + length qs) ∉ (fmap ((λ{ (x , y) → x + y })) (addX qs))
  × (length qs + n - q) ∉ (fmap ((λ{ (x , y) → (x + n) - y })) (addX qs))


_[_]AreNotAttacking?_ : (qs : List ℕ) → (n : ℕ) → (q : ℕ) → Dec (qs [ n ]AreNotAttacking q)
qs [ n ]AreNotAttacking? q = f (_ ∉? _ ) (f (_ ∉? _) (_ ∉? _))
  where
    f : {P : Set} → {Q : Set} → Dec P → Dec Q → Dec (P × Q)
    f (yes p) (yes p₁) = yes (p , p₁)
    f (yes p) (no ¬p) = no λ x → ¬p (proj₂ x)
    f (no ¬p) dq = no λ x → ¬p (proj₁ x)


queensCasual : ℕ → ℕ → List (List ℕ)
queensCasual n zero = [] ∷ []
queensCasual n (suc k) =
  do
    qs ← queensCasual n k
    q ← filter (λ q → qs [ n ]AreNotAttacking? q) (range n)
    return (q ∷ qs)


-- first {{{

module first where
  queensCasualProven : (n : ℕ) → (k : ℕ) → LiftProp.LiftProp (PeacefulQueens n) (queensCasual n k)
  queensCasualProven n zero = ⟦ ( ([] , ⟦ [] <> refl ⟧ , tt , tt) ∷ []) <> refl ⟧
  queensCasualProven n (suc k) =
    let
      _>>=_ = _>>=LP_
      return = returnLP
    in
    do
      (qs , qsp) ← queensCasualProven n k
      (q , (qp₁ , qp₂)) ← (filterLPT (λ q → qs [ n ]AreNotAttacking? q) (rangeLP n))
      return (q ∷ qs , ({!!} , {!!} , {!!}))


-- }}}

-- suggested _∧LP_ by dominique {{{

queensCasualProven : (n : ℕ) → (k : ℕ) → LiftProp (PeacefulQueens n) (queensCasual n k)
queensCasualProven n zero = ⟦ ( ([] , ⟦ [] <> refl ⟧ , tt , tt) ∷ []) <> refl ⟧
queensCasualProven n (suc k) =
  let
    _>>=_ = _>>=LP_
    return = returnLP
    open LiftProp.List
  in
  do
    (qs , qsp) ← queensCasualProven n k
    (q , (qp₁ , qp₂)) ← let
                          ps = filter (λ q → qs [ n ]AreNotAttacking? q) (range n)
                        in {!!} ∧LP {!!}
    return (q ∷ qs , ({!!} , {!!} , {!!}))


-- }}}

-- custom application? {{{



-- }}}

-- queens again {{{




-- }}}
