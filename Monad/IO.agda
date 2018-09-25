module Monad.IO where

open import Imports hiding (_++_)

open import Monad public

open import Agda.Builtin.IO public
open import Agda.Builtin.String public

postulate
  putStrLn : String → IO ⊤
  getLine : IO String
  returnIO : ∀ {a} {A : Set a} → A → IO A
  _>>=IO_  : ∀ {a b} {A : Set a} {B : Set b} → IO A → (A → IO B) → IO B

{-# FOREIGN GHC import qualified Data.Text.IO as Text #-}
{-# COMPILE GHC putStrLn = Text.putStrLn #-}
{-# COMPILE GHC getLine = Text.getLine #-}
{-# COMPILE GHC returnIO = \_ _ -> return    #-}
{-# COMPILE GHC _>>=IO_  = \_ _ _ _ -> (>>=) #-}

postulate -- trusting haskells IO implementation, we postulate these things about IO
  ioMLaw1 : ∀{X Y : Set} → (f : X → IO Y) (x : X) → (returnIO x >>=IO f) ≡ f x
  ioMLaw2 : ∀{X : Set} → (mx : IO X) → mx >>=IO returnIO ≡ mx
  ioMLaw3 : ∀{X Y Z : Set} → (g : X → IO Y) → (f : Y → IO Z) → (mx : IO X) →
              (mx >>=IO g) >>=IO f ≡ mx >>=IO (λ x → g x >>=IO f)

instance
  ioMonad : Monad IO
  Monad.return ioMonad = returnIO
  Monad._>>=_ ioMonad = _>>=IO_
  Monad.leftId ioMonad = ioMLaw1
  Monad.rightId ioMonad = ioMLaw2
  Monad.assoc ioMonad = ioMLaw3

_++_ : String → String → String
s ++ t with primStringToList s | primStringToList t
s ++ t | s' | t' = primStringFromList (s' Data.List.++ t')
  where
    open import Data.List

{-# DISPLAY _>>=IO_ a b = a >>= b #-}
{-# DISPLAY returnIO = return #-}
