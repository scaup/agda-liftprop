# Code samples to accompany the functional pearl titled "How to `do` proofs?"

## Get started quickly

The `Playground` file imports all the necessary modules to define your own computations and to state and prove your own properties about them.

## Tested with versions 

Tested with Agda version 2.6.0, and std-lib v1.0

## Directory Structure

* `FunctorTC.agda`, `ApplicativeTC.agda` and `MonadTC.agda`

  Basic definitions of `Functor`, `Applicative`, and `Monad` type classes.

* `Functors/`, `Applicatives/`, `Monads/`

  Directories containing instances of each type class.

* `FunctorLift.agda`

  Implementation of `Lift`, `fmapL`, `applyL`, `fmapR` etc.

* `ApplicativeLift.agda`

  Implementation of `pureL` and `_<*>L_` and `_<*>R_`.

* `MonadLift.agda`

  Implementation of `returnL`, `_>>=L_`, `_>>=R_` etc.

* `Examples/`

  Worked out examples from in the paper.

* `Playground.agda`

  The aforementioned playground.

* `PullbackPreserving.agda`

  Type class for pullback preserving functors and some instances

* `Exp/`
  - `Hoare.agda`: Implementation of Swierstra's Hoare monad (`_>>=H_`)
  - `HoareLift.agda`: A specified notion of `Lift`, and a lifted bind for (`_>>=H_`)
  - `Continuation.agda`: `_,L_` for decidable properties with the continuation monad
