{-# OPTIONS --allow-unsolved-metas #-}

open import Monad
open import Monad.State
open import Imports

data Tree (A : Set) : Set where
  leaf : (a : A) → Tree A
  node : Tree A → Tree A → Tree A

treeToList : {A : Set} → Tree A → List A
treeToList (leaf a) = a ∷ []
treeToList (node l r) = treeToList l ++ treeToList r

-- relabel tree {{{

fresh : State ℕ ℕ
runState fresh n = n , suc n -- returning state, and modifying it plus 1 (A × S)

label : {A : Set} → Tree A → State ℕ (Tree ℕ)
label (leaf a) = do
                    n ← fresh
                    return (leaf n)
label (node l r) = do
                        l' ← label l
                        r' ← label r
                        return (node l' r')

-- }}}

-- example trees {{{

exampleTree : Tree Bool
exampleTree = node (leaf true) (node (node (leaf false) (leaf false)) (leaf true))

exampleTree' : Tree Bool
exampleTree' = node (leaf true) (leaf true)

exTree : Tree Bool
exTree = node (node (leaf false) (leaf true)) (node (node (leaf true) (node (leaf false) (leaf true))) (leaf false))

exampleTree'' : Tree ℕ
exampleTree'' = node (leaf 0) (leaf 5)

exTree' : Tree ℕ
exTree' = node (node (leaf 3) (leaf 9)) (node (node (leaf 9) (node (leaf 9) (leaf 9))) (leaf 9))

-- }}}

data _≅_ {A B : Set} : (ta : Tree A) → (tb : Tree B) → Set where
  leafISO : {a : A} → {b : B} → leaf a ≅ leaf b
  nodesISO : {tal tar : Tree A} → {tbl tbr : Tree B} → tal ≅ tbl → tar ≅ tbr → node tal tar ≅ node tbl tbr

pro : exTree' ≅ exTree
pro = nodesISO (nodesISO leafISO leafISO) (nodesISO (nodesISO leafISO (nodesISO leafISO leafISO)) leafISO)


-- non-interesting {{{

_≠_ : ℕ → ℕ → Set
n ≠ m = n ≡ m → ⊥

_elem_ : ℕ → List ℕ → Bool
n elem [] = false
n elem (x ∷ xs) with n ≟ x
n elem (x ∷ xs) | yes p = true
n elem (x ∷ xs) | no ¬p = false ∨ (n elem xs)

NoDupsTree : Tree ℕ → Set
NoDupsTree t = nodups (treeToList t) ≡ true
  where
    nodups : List ℕ → Bool
    nodups [] = true
    nodups (x ∷ xs) = (not (x elem xs)) ∧ nodups xs

data _IsUpperBoundFor_ (n : ℕ) : (Tree ℕ) → Set where
  leafBound : {m : ℕ} → m ≤ n → n IsUpperBoundFor (leaf m)
  leftAndRightBound : ∀{l r} → n IsUpperBoundFor l → n IsUpperBoundFor r → n IsUpperBoundFor (node l r)

data _IsLowerBoundFor_ (n : ℕ) : (Tree ℕ) → Set where
  leafBound : {m : ℕ} → n ≤ m → n IsLowerBoundFor (leaf m)
  leftAndRightBound : ∀{l r} → n IsLowerBoundFor l → n IsLowerBoundFor r → n IsLowerBoundFor (node l r)

-- }}}

-- uninteresting helper lemma's  {{{

n≤m=>pn≤pm : {n m : ℕ} → n ≤ m → pred n ≤ pred m
n≤m=>pn≤pm = {!!}

n≤n : {n : ℕ} → n ≤ n
n≤n {zero} = z≤n
n≤n {suc n} = s≤s (n≤n)

n≤sucn : {n : ℕ} → n ≤ suc n
n≤sucn {zero} = z≤n
n≤sucn {suc n} = s≤s n≤sucn

sucn≠0 : {n : ℕ} → suc n ≠ 0
sucn≠0 {n} = λ x → {!!}

sucm&m≤n=>n≠0 : {n m : ℕ} → suc m ≤ n → n ≠ 0
sucm&m≤n=>n≠0 = {!!}

n≡m=>n≤m : {n m : ℕ} → n ≡ m → n ≤ m
n≡m=>n≤m refl = n≤n

n≤o→pn≤po : {n o : ℕ} → n ≤ o → pred n ≤ pred o
n≤o→pn≤po {.0} {o} z≤n = z≤n
n≤o→pn≤po {.(suc _)} {.(suc _)} (s≤s eq) = eq

n≡m→n≤o→m≤o : {n m o : ℕ} → n ≡ m → n ≤ o → m ≤ o
n≡m→n≤o→m≤o refl u = u

n≡m&sm≡o : ∀{n m o} → m ≡ n → suc m ≡ o → n ≤ o
n≡m&sm≡o {zero} refl refl = z≤n
n≡m&sm≡o {suc n} refl refl = s≤s ((n≡m&sm≡o refl refl))

sn≡m : ∀{n m} → suc n ≡ m → n ≤ m
sn≡m {zero} refl = z≤n
sn≡m {suc n} refl = s≤s (sn≡m refl)

n≡mubt : ∀{n m t} → n ≡ m → n IsUpperBoundFor t → m IsUpperBoundFor t
n≡mubt refl lb = lb

n≡mlbt : ∀{n m t} → n ≡ m → n IsLowerBoundFor t → m IsLowerBoundFor t
n≡mlbt refl lb = lb

n≠0→spn≡n : {n : ℕ} → (n ≡ 0 → ⊥) → n ≡ suc (pred n)
n≠0→spn≡n {zero} f = {!!}
n≠0→spn≡n {suc n} f = refl

n≡m→m≠0→n≠0 : {n m : ℕ} → (m ≡ n) → (n ≡ 0 → ⊥) → (m ≡ 0 → ⊥)
n≡m→m≠0→n≠0 refl f = f

transitivity : ∀{m n o} → m ≤ n → n ≤ o → m ≤ o
transitivity = {!!}

transitivity' : ∀{m m' n n' o o'} → m ≡ m' → n ≡ n' → o ≡ o' → m ≤ n → n' ≤ o → m' ≤ o'
transitivity' = {!!}

llbt : ∀{x y t} → x ≤ y → y IsLowerBoundFor t → x IsLowerBoundFor t
llbt z≤n (leafBound x) = leafBound z≤n
llbt z≤n (leftAndRightBound lb lb₁) = leftAndRightBound (llbt z≤n lb) (llbt z≤n lb₁)
llbt (s≤s sm) (leafBound (s≤s x)) = leafBound (s≤s (transitivity sm x))
llbt (s≤s sm) (leftAndRightBound lb lb₁) = leftAndRightBound (llbt (s≤s sm) lb) (llbt (s≤s sm) lb₁)

uubt : ∀{x y t} → x ≤ y → x IsUpperBoundFor t → y IsUpperBoundFor t
uubt eq (leafBound x₁) = leafBound (transitivity x₁ eq)
uubt eq (leftAndRightBound ub ub₁) = leftAndRightBound (uubt eq ub) (uubt eq ub₁)

-- }}}

meatOfIt : {l r : Tree ℕ} → {n : ℕ} → (n ≠ 0) → (pred n) IsUpperBoundFor l → n IsLowerBoundFor r → (NoDupsTree l) → (NoDupsTree r) → NoDupsTree (node l r)
meatOfIt l≤x r≥x+1 lnd rnd = {!!}

record Type (n₁ : ℕ) (n₂ : ℕ) : Set where
  field
    n₂NotZero : n₂ ≠ 0
    initial≤final : n₁ ≤ n₂
    finalTree : Tree ℕ
    proofLower : n₁ IsLowerBoundFor finalTree
    proofUpper : (pred n₂) IsUpperBoundFor finalTree
    proofNoDups : NoDupsTree finalTree

open Type public

record Proof (t : Tree ℕ) (n₁ : ℕ) (n₂ : ℕ) : Set where
  field
    n₂NotZero : n₂ ≠ 0
    initial≤final : n₁ ≤ n₂
    proofLower : n₁ IsLowerBoundFor t
    proofUpper : (pred n₂) IsUpperBoundFor t
    proofNoDups : NoDupsTree t

open Proof public
