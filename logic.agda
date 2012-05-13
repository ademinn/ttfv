module logic where
open import Data.List

module dummy (V : Set) where

  postulate _∈_ : (x : V) → (g : List V) → Set
  postulate ⊥c : V
  postulate _─_ : List V → V → List V

  data _⊢_ : List V → V → Set where
    Ax : ∀ Γ φ → φ ∈ Γ → Γ ⊢ φ
    Bot : ∀ Γ φ → Γ ⊢ ⊥c → Γ ⊢ φ  
