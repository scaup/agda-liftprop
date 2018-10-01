module Voting where

open import Monad.IO
open import Monad.List
open import LiftProp

-- stdlib {{{

open import Data.Nat
open import Data.List
open import Data.Bool hiding (_≟_; _∧_)
open import Data.Product hiding (zip)
open import Data.Unit hiding (_≟_; _≤?_; _≤_)
open import Data.Empty
open import Data.Sum
open import Function

open import Relation.Unary using (Decidable)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

-- }}}


postulate
  Person : Set
  -- Peson contain some kind of public key, with which a certificate is generated

  voters : List Person
  Candidate : Set
  Certificate : Set

Ballot = Candidate × Certificate

postulate
  getBallotOf : Person → IO Ballot

  ValidBallotOf : Person → Predicate Ballot
  -- validates if the certificate with the public key of the person or something..

  ValidGetBallotOf : (person : Person) → LiftProp (ValidBallotOf person) (getBallotOf person)

  selectWinner : (List Ballot) → Candidate

  parallel : {A : Set} → List (IO A) → IO (List A)
  -- Suppose a library function

  parallelLP : {A : Set} → {ioa|s : List (IO A)} → {P : Predicate A} →
    LiftProp (LiftProp P) ioa|s → LiftProp (LiftProp P) (parallel ioa|s)
  -- Along with parallel, our library also exports...


OneEach : List Ballot → Set
OneEach bs = fmap {!!} (fmap (λ{ (b , p) → {!!}}) (zip bs voters)) ≡ bs

test : LiftProp OneEach (parallel (fmap getBallotOf voters))
monadicValueX test = {!!}
proofPPE test = {!!}

election : IO Candidate
election =
  do
    bs ← parallel (fmap getBallotOf voters)
    return $ selectWinner bs


ElectionFair : LiftProp {!!} election
ElectionFair =
  let
    _>>=_ = _>>=LP_
    return = returnLP
  in
  do
    (bs , (p₁ , p₂)) ← (parallelLP {P = {!!}} do -- fmapLP?
                     (v , _) ← toLP voters
                     returnLP ( getBallotOf v , {!!}))
               ∧LP test
    {!!}


