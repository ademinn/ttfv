module SimpleMath where

open import Data.Nat

data Coin : Set where
  CTrue CFalseLight CFalseHeavy : Coin

-- \~=
data _≅_ : Coin → Coin → Set where
  CEqTrue       : CTrue       ≅ CTrue
  CEqFalseLight : CFalseLight ≅ CFalseLight
  CEqFalseHeavy : CFalseHeavy ≅ CFalseHeavy

-- \<~
data _≲_ : Coin → Coin → Set where
  CLessFLT  : CFalseLight ≲ CTrue
  CLessFLFH : CFalseLight ≲ CFalseHeavy
  CLessTFH  : CTrue       ≲ CFalseHeavy

-- List that contains n CTrue, n₁ CFalseLight and n₂ CFalseHard
data CoinTFLHList : ℕ → ℕ → ℕ → Set where
  C[]   : CoinTFLHList zero zero zero
  +T_  : {n n₁ n₂ : ℕ} → CoinTFLHList n n₁ n₂ → CoinTFLHList (suc n) n₁ n₂
  +FL_ : {n n₁ n₂ : ℕ} → CoinTFLHList n n₁ n₂ → CoinTFLHList n (suc n₁) n₂
  +FH_ : {n n₁ n₂ : ℕ} → CoinTFLHList n n₁ n₂ → CoinTFLHList n n₁ (suc n₂)

data Either3 (A B C : Set) : Set where
  left   : A → Either3 A B C
  middle : B → Either3 A B C
  right  : C → Either3 A B C

-- \::-
--_∺_ : 

{--
C[_] :  → Coin → CoinTFLHList ℕ ℕ ℕ
C[ CTrue ] = {!+T ?!}
C[ CFalseLight ] = {!!}
C[ CFalseHeavy ] = {!!}
--}

_C++_ : ∀ {n₁ n₂ n₁₁ n₁₂ n₂₁ n₂₂} → (CoinTFLHList n₁ n₁₁ n₁₂) → (CoinTFLHList n₂ n₂₁ n₂₂) → (CoinTFLHList (n₁ + n₂) (n₁₁ + n₂₁) (n₁₂ + n₂₂))
C[] C++ CL₂       = CL₂
(+T_ y) C++ CL₂  = +T (y C++ CL₂)
(+FL_ y) C++ CL₂ = +FL (y C++ CL₂)
(+FH_ y) C++ CL₂ = +FH (y C++ CL₂)