module Simply-Typed where

open import Data.List
open import Data.String
open import Level
open import Data.Empty using (⊥)
open import Data.Unit using (⊤)

-- ↝ \r~
infixr 5 _⇝_
data Type : Set where
  con : String → Type
  _⇝_ : Type → Type → Type

TList = List Type

-- ∈ is \in
infixr 4 _∈_

data _∈_ {a} {A : Set a} : A → List A → Set a where
  Z : ∀ {x xs} → x ∈ (x ∷ xs)
  S : ∀ {x y xs} → (n : x ∈ xs) → x ∈ (y ∷ xs)

-- ∙ is \.
-- ∷ is \::
infixl 5 _∙_
data Term (Γ : TList) : Type → Set where
  Var : ∀ {A} → A ∈ Γ → Term Γ A
  Λ   : ∀ {A B} → Term (A ∷ Γ) B → Term Γ (A ⇝ B)
  _∙_ : ∀ {A B} → Term Γ (A ⇝ B) → Term Γ A → Term Γ B

-- ⊆ is \sub=
_⊆_ : ∀ {a} {A : Set a} → List A → List A → Set a
xs ⊆ ys = ∀ {x} → x ∈ xs → x ∈ ys

-- ≡ is \==
data _≡_ {l : Level} {A : Set l} : A → A → Set l where
  Refl : {a : A} → (a ≡ a)

⊆cong : ∀ {a} {A : Set a} {x y : A} {xs ys : List A} → x ≡ y → (xs ⊆ ys) → ((x ∷ xs) ⊆ (y ∷ ys))
⊆cong (Refl {x}) f Z = Z
⊆cong refl f (S n) = S (f n)

xs⊆x∷xs : ∀ {a} {A : Set a} {y : A} {xs : List A} → (xs ⊆ (y ∷ xs))
xs⊆x∷xs = S

x∷y∷s⊆y∷x∷s : ∀ {a} {A : Set a} {x y : A} {s : List A} → ((x ∷ y ∷ s) ⊆ (y ∷ x ∷ s))
x∷y∷s⊆y∷x∷s Z = S Z
x∷y∷s⊆y∷x∷s (S Z) = Z
x∷y∷s⊆y∷x∷s (S (S n)) = S (S n)

x∈s,x∷s⊆s : ∀ {a} {A : Set a} {x : A} {s : List A} → (x ∈ s) → ((x ∷ s) ⊆ s)
x∈s,x∷s⊆s m Z = m
x∈s,x∷s⊆s m (S n) = n

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

-- ⊹ is \+' '
_⊹_ : ∀ {a} {A : Set a} → List A → List A → List A
l1 ⊹ l2 = Data.List._++_ l1 l2
infixr 5 _⊹_

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