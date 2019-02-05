{-# OPTIONS --allow-unsolved-metas #-}

module Functors.IO where

open import FunctorTC
open import Postulates

-- stdlib {{{

open import Data.Unit hiding (_≟_; _≤?_; _≤_)
open import Function

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- }}}

open import Agda.Builtin.IO public
open import Agda.Builtin.String public

postulate
  putStrLn : String → IO ⊤
  getLine : IO String
  returnIO : ∀ {a} {A : Set a} → A → IO A
  _>>=IO_  : ∀ {a b} {A : Set a} {B : Set b} → IO A → (A → IO B) → IO B
  leftIdIO : ∀{X Y : Set} → (f : X → IO Y) (x : X) → (returnIO x >>=IO f) ≡ f x
  rightIdIO : ∀{X : Set} → (mx : IO X) → mx >>=IO returnIO ≡ mx
  assocIO : ∀{X Y Z : Set} → (g : X → IO Y) → (f : Y → IO Z) → (mx : IO X) →
              (mx >>=IO g) >>=IO f ≡ mx >>=IO (λ x → g x >>=IO f)

{-# FOREIGN GHC import qualified Data.Text.IO as Text #-}
{-# COMPILE GHC putStrLn = Text.putStrLn #-}
{-# COMPILE GHC getLine = Text.getLine #-}
{-# COMPILE GHC returnIO = \_ _ -> return    #-}
{-# COMPILE GHC _>>=IO_  = \_ _ _ _ -> (>>=) #-}

fmapIO : {X Y : Set} → (X → Y) → IO X → IO Y
fmapIO f mx = mx >>=IO (returnIO ∘ f)

instance
  ioFunctor : Functor IO
  Functor.fmap ioFunctor = fmapIO
  Functor.composition ioFunctor g f mx = begin
                                           mx >>=IO (returnIO ∘ f ∘ g)
                                         ≡⟨ cong (_>>=IO_ mx) (sym (funext (λ x → leftIdIO _ _))) ⟩
                                           mx >>=IO (λ x → returnIO (g x) >>=IO (returnIO ∘ f))
                                         ≡⟨ sym (assocIO _ _ _) ⟩
                                           ((mx >>=IO (returnIO ∘ g)) >>=IO (returnIO ∘ f)) ∎
  Functor.unit ioFunctor = rightIdIO _
