{-# OPTIONS --allow-unsolved-metas #-} 

module Monad.StateIO where

open import Imports
open import Monad public
open import Monad.IO

record StateIO (S A : Set) : Set where
  field
    runStateIO : (S → IO (A × S))

open StateIO public

instance
  stateioMonad : {S : Set} → Monad (StateIO S)
  runStateIO (Monad.return stateioMonad x) s = return (x , s)
  runStateIO ((stateioMonad Monad.>>= record { runStateIO = k }) f) s =
    do
      (x , s') ← k s
      runStateIO (f x) s'
  Monad.leftId stateioMonad = {!!}
  Monad.rightId stateioMonad = {!!}
  Monad.assoc stateioMonad = {!!}

lift : {A S : Set} → IO A → StateIO S A
runStateIO (lift act) s = do
  a ← act
  return (a , s)

getSIO : {S : Set} → StateIO S S
runStateIO getSIO s = return (s , s)

putSIO : {S : Set} → (s : S) → StateIO S ⊤
runStateIO (putSIO s) s' = return (tt , s)

modifySIO : {S : Set} → (f : S → S) → StateIO S ⊤
runStateIO (modifySIO f) s = return (tt , f s)

modify-dependSIO : {S : Set} → (f : S → S) → StateIO S (Σ[ old ∈ S ] (Σ[ new ∈ S ] (f old ≡ new)))
runStateIO (modify-dependSIO f) s = return ((s , f s , refl) , f s)

evalStateIO : ∀{S A} → StateIO S A → S → IO A
evalStateIO record { runStateIO = k } s = fmap proj₁ (k s)

execStateIO : ∀{S A} → StateIO S A → S → IO S
execStateIO record { runStateIO = k } s = fmap proj₂ (k s)
