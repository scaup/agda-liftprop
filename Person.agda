module Person where

open import LiftProp hiding (LiftProp) --hiding LiftProp is necessary; ambiguity between record and module name

open import Monad.IO hiding (_>>=_ ; return)
open import Data.Product

postulate
  Name : Set
  Age : Set

record Person : Set where
  constructor _,_
  field
    name : Name
    age : Age

postulate
  getName : IO Name
  getAge : IO Age

getPerson : IO Person
getPerson =
  do
    name ← getName
    age ← getAge
    return (name , age)
  where
    open Monad.IO

postulate
  NameIsValid : Predicate Name
  AgeIsValid : Predicate Age

PersonIsValid : LiftProp.Predicate Person
PersonIsValid = λ{ (name , age ) → NameIsValid name × AgeIsValid age}

postulate
  getNameValid : LiftProp.LiftProp NameIsValid getName
  getAgeValid : LiftProp.LiftProp AgeIsValid getAge

getPersonValid : LiftProp.LiftProp PersonIsValid getPerson
getPersonValid =
  do
    (name , p) ← getNameValid
    (age , q) ← getAgeValid
    return (((name , age)) , (p , q))
  where
    open LiftProp renaming
         (_>>=LP_ to _>>=_ ;
         returnLP to return)
