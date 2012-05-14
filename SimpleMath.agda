module SimpleMath where

open import Data.Nat

data Coin : Set where
  CTrue CFalseLight CFalseHeavy : Coin

data _≅_ : Coin → Coin → Set where
  CEqTrue       : CTrue       ≅ CTrue
  CEqFalseLight : CFalseLight ≅ CFalseLight
  CEqFalseHeavy : CFalseHeavy ≅ CFalseHeavy

data _≲_ : Coin → Coin → Set where
  CLessFLT  : CFalseLight ≲ CTrue
  CLessFLFH : CFalseLight ≲ CFalseHeavy
  CLessTFH  : CTrue       ≲ CFalseHeavy