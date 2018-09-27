module Prime where

open import Data.Nat
open import Data.Nat.Primality
open import Data.List
open import Monad.List

open import LiftProp

primesTo : ℕ → List ℕ
primesTo m = {!!}

first_primes : ℕ → List ℕ
first n primes = {!!}

primesToProven : (n : ℕ) → LiftProp Prime (primesTo n)
primesToProven n = {!!}

firstnprimesProven : (n : ℕ) → LiftProp Prime (first n primes)
firstnprimesProven = {!!}
