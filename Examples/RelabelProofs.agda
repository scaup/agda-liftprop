module Examples.RelabelProofs where

open import Examples.Relabel

open import Monads.IO
open import Functors.IO
open import Functors.List
open import Monads.List
open import Lift
open import Lift.MonadTC renaming (_>>=L_ to _>>=_; returnL to return)
open import Postulates

-- stdlib {{{

open import Data.List
open import Data.Nat
open import Data.Product

-- }}}

postulate

relabel≅ : {A : Set} → (t : Tree A) → Lift (λ t' → t ≅ t') (relabel t)
relabel≅ (leaf a) = do
                      n , _ ← nothing2Prove fresh
                      return (leaf n , leafISO) -- (leaf n ,  leafISO)
relabel≅ (node l r) = do
                        pl≡l' ← relabel≅ l
                        pr≡r' ← relabel≅ r
                        return (nodesISO pl≡l' pr≡r')

