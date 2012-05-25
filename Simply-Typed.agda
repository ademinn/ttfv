module Simply-Typed where

open import Data.List
open import Data.String
open import Level
open import ListProofs
open import Data.Empty using (⊥)
open import Data.Unit using (⊤)

-- ↝ \r~
infixr 5 _↝_
data Type : Set where
  con : String → Type 
  _↝_ : Type → Type → Type

TList = List Type

-- ∙ is \.
-- ∷ is \::
infixl 5 _∙_
data Term (Γ : TList) : Type → Set where
  Var : ∀ {A} → A ∈ Γ → Term Γ A
  Λ   : ∀ {A B} → Term (A ∷ Γ) B → Term Γ (A ↝ B)
  _∙_ : ∀ {A B} → Term Γ (A ↝ B) → Term Γ A → Term Γ B

wk : ∀ {Γ Δ A} → (Γ ⊆ Δ) → Term Γ A → Term Δ A
wk θ (Var y) = Var (θ y)
wk θ (y₁ ∙ y₂) = wk θ y₁ ∙ wk θ y₂
wk θ (Λ y) = Λ (wk (⊆cong Refl θ) y)

weaking : ∀ {Γ A B} → Term Γ B → Term (A ∷ Γ) B
weaking = wk xs⊆x∷xs

exchange : ∀ {Γ A B C} → Term (A ∷ B ∷ Γ) C → Term (B ∷ A ∷ Γ) C
exchange = wk x∷y∷s⊆y∷x∷s

contraction : ∀ {Γ A B} → Term (A ∷ A ∷ Γ) B → Term (A ∷ Γ) B
contraction = wk (x∈s,x∷s⊆s Z)

substitution : ∀ {Γ A C} → Term Γ A → Term (A ∷ Γ) C → Term Γ C
substitution = term-substitution [] _
  where
    term-substitution : ∀ {A C} (Γ Γ' : TList) →
      Term Γ' A → Term (Γ ⊹ [ A ] ⊹ Γ') C → Term (Γ ⊹ Γ') C
    term-substitution Γ Γ' tm (Var y) = var-substitution Γ Γ' tm y
      where
        var-substitution : ∀ {A C} (Γ Γ' : TList) →
          Term Γ' A → (C ∈ (Γ ⊹ [ A ] ⊹ Γ')) → Term (Γ ⊹ Γ') C
        var-substitution [] Γ' t Z = t
        var-substitution [] Γ' t (S n) = Var n
        var-substitution (x ∷ Γs) Γ' t Z = Var Z
        var-substitution (x ∷ Γs) Γ' t (S n) = weaking (var-substitution Γs Γ' t n)
    term-substitution Γ Γ' tm (Λ y) = Λ (term-substitution (_ ∷ Γ) Γ' tm y)
    term-substitution Γ Γ' tm (y₁ ∙ y₂) = term-substitution Γ Γ' tm y₁ ∙ term-substitution Γ Γ' tm y₂

data isRedex {Γ P} : Term Γ P → Set where
  con : ∀ {σ} (t1 : Term (σ ∷ Γ) P) → (t2 : Term Γ σ) → isRedex ((Λ t1) ∙ t2)

{-
check : ∀ {Γ P} → Term Γ P → Set
check ( (Λ _ ) ∙ _ ) = ⊤
check _ = ⊥

β-reduction : ∀ {Γ P} (t : Term Γ P) → (check t) → Term Γ P
--  → ( (Λ (Term (σ ∷ Γ) P) ) ∙ (Term Γ σ) ) → Term Γ P
β-reduction (Var y) ()
β-reduction (Λ y) ()
β-reduction (Var y ∙ y') ()
β-reduction (y ∙ y' ∙ y0) ()
β-reduction (Λ y₁ ∙ y₂) ct = substitution y₂ y₁
-}

data Redex {Γ A} : Term Γ A → Set where
  skip2l : ∀ {B} {t1 : Term (B ∷ Γ) A} {t2 : Term Γ B} → Redex t1 → Redex ((Λ t1) ∙ t2)

{-
data Re : Term → Set where
  skip2l : ∀ M N → Re M → Re (M ∙ N)
  skip2r : ∀ M N → Re N → Re (M ∙ N)
  skipth : ∀ x M → Re M → Re (Λ x ⟶ N)
  this : ∀ x M N → Re ((Λ x ⟶ M) ∙ N)

applyreduction (M : Preterm) → Re M → PreTerm

-}
