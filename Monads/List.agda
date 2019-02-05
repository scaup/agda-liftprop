{-# OPTIONS --allow-unsolved-metas #-}

module Monads.List where

open import MonadTC

open import FunctorTC
open import Functors.List

open import Data.List
open import Data.List.Properties
open import Relation.Binary.PropositionalEquality hiding ([_])

instance
  listMonad : Monad List
  Monad.return listMonad x = [ x ]
  (listMonad Monad.>>= []) f = []
  (listMonad Monad.>>= (x ∷ xs)) f = f x ++ xs >>= f
  Monad.leftId listMonad f x with f x
  Monad.leftId listMonad f x | [] = refl
  Monad.leftId listMonad f x | x₁ ∷ fx = cong (_∷_ x₁) (++-identityʳ fx)
  Monad.rightId listMonad = {!!}
  Monad.assoc listMonad = {!!}
  Monad.functorM listMonad = listFunctor
  Monad.compatiblefmap listMonad {X} {Y} {f} {[]} = refl
  Monad.compatiblefmap listMonad {X} {Y} {f} {x ∷ as} = cong (_∷_ (f x)) (compatiblefmap {_} {X} {Y} {f} {as})
