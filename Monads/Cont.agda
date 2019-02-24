module Monads.Cont where

open import MonadTC
open import Applicatives.Cont
open import Functors.Cont

open import Function
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning


instance
  contMonad : {C : Set} → Monad (Cont C)
  open Monad
  applicativeM contMonad = contApplicative
  _>>=_ contMonad cx f = λ k → cx (λ x → (f x) k)
  leftId contMonad f x = refl
  rightId contMonad cx = refl
  assoc contMonad g f mx = refl
  compatible<*> contMonad cf cx = refl
