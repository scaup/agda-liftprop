module Examples.RelabelProofIsomorphic where

open import Examples.Relabel

open import Monads.IO
open import Functors.IO
open import Functors.State
open import Monads.State
open import Lift
open import Lift.MonadTC renaming (_>>=L_ to _>>=_; returnL to return)
open import Postulates

-- stdlib {{{

open import Data.List
open import Data.Nat
open import Data.Product

-- }}}

data _≅_ {A B : Set} : Tree A → Tree B → Set where
  leafISO : {a : A} → {b : B} → leaf a ≅ leaf b
  nodesISO : {tal tar : Tree A} → {tbl tbr : Tree B} → tal ≅ tbl → tar ≅ tbr → node tal tar ≅ node tbl tbr

isomorphicEx : exampleTree ≅ evalState (relabel exampleTree) 6
isomorphicEx = nodesISO leafISO (nodesISO (nodesISO leafISO leafISO) leafISO)

relabel≅ : {A : Set} → (t : Tree A) → Lift (λ t' → t ≅ t') (relabel t)
relabel≅ (leaf a) = do
                      (n , _) ← nothing2Prove fresh
                      return (leaf n , leafISO)
relabel≅ (node l r) = do
                        (l' , pl≡l') ← relabel≅ l
                        (r' , pr≡r') ← relabel≅ r
                        return (node l' r' , nodesISO pl≡l' pr≡r')

