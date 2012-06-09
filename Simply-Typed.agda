module Simply-Typed where

open import Data.List
open import Data.String
open import Level
open import ListProofs
open import Data.Empty using (⊥)
open import Data.Unit using (⊤)

-- ↝ is \r~
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

data Redex {Γ} : {A : Type} → Term Γ A → Set where
  this    : ∀ {σ A} → (t₁ : Term (σ ∷ Γ) A) → (t₂ : Term Γ σ) → Redex ((Λ t₁) ∙ t₂)
  skip2l  : ∀ {σ A} → (t₁ : Term Γ (σ ↝ A)) → (t₂ : Term Γ σ) → Redex t₁ → Redex (t₁ ∙ t₂)
  skip2r  : ∀ {σ A} → (t₁ : Term Γ (σ ↝ A)) → (t₂ : Term Γ σ) → Redex t₂ → Redex (t₁ ∙ t₂)
  skipth : ∀ {σ A} → (t : Term (σ ∷ Γ) A) → Redex t → Redex (Λ t)

applyReduction : {A : Type} {Γ : TList} {t : Term Γ A} → Redex t → Term Γ A
applyReduction (this t₁ t₂)  = substitution t₂ t₁
applyReduction (skip2l _ t₂ r) = (applyReduction r) ∙ t₂
applyReduction (skip2r t₁ _ r) = t₁ ∙ (applyReduction r)
applyReduction (skipth t r) = Λ (applyReduction r)

data _→β_ {Γ} : {A : Type} → Term Γ A → Term Γ A → Set where
  reduce : ∀ {A} (t : Term Γ A) → (r : Redex t) → t →β (applyReduction r)
--  Λβ : ∀ {σ A} {t₁ t₂ : Term (σ ∷ Γ) A} → t₁ →β t₂ → (Λ t₁) →β (Λ t₂)
--  leftβ : ∀ {A B} {t₁ t₂ : Term Γ (A ↝ B)} → (t : Term Γ A) → t₁ →β t₂ → (t₁ ∙ t) →β (t₂ ∙ t)
--  rightβ : ∀ {A B} {t₁ t₂ : Term Γ A} → (t : Term Γ (A ↝ B)) → t₁ →β t₂ → (t ∙ t₁) →β (t ∙ t₂)


skip2lProof : ∀ {σ Γ A} {t₁ t₂ : Term Γ (σ ↝ A)} → (t' : Term Γ σ) → t₁ →β t₂ → (t₁ ∙ t') →β (t₂ ∙ t')
skip2lProof t' (reduce t r) = reduce (t ∙ t') (skip2l t t' r)

skip2rProof : ∀ {σ Γ A} {t₁ t₂ : Term Γ σ} → (t' : Term Γ (σ ↝ A)) → t₁ →β t₂ → (t' ∙ t₁) →β (t' ∙ t₂)
skip2rProof t' (reduce t r) = reduce (t' ∙ t) (skip2r t' t r)

skipthProof : ∀ {σ Γ A} {t₁ t₂ : Term (σ ∷ Γ) A} → t₁ →β t₂ → (Λ t₁) →β (Λ t₂)
skipthProof (reduce t r) = reduce (Λ t) (skipth t r)


data _↠β_ {Γ A} : Term Γ A → Term Γ A → Set where
  consβ : (t : Term Γ A) → t ↠β t
  succβ : ∀ {t₁ t₂ t₃} → t₁ ↠β t₂ → t₂ →β t₃ → t₁ ↠β t₃

head : ∀ {Γ A} {t₁ t₂ : Term Γ A} → t₁ ↠β t₂ → Term Γ A
head (consβ t) = t
head (succβ t _) = head t

tail : ∀ {Γ A} {t₁ t₂ : Term Γ A} → t₁ ↠β t₂ → Term Γ A
tail (consβ t) = t
tail (succβ _ (reduce t r)) = applyReduction r

skip2lProof' : ∀ {σ Γ A} {t₁ t₂ : Term Γ (σ ↝ A)} → (t' : Term Γ σ) → t₁ ↠β t₂ → (t₁ ∙ t') ↠β (t₂ ∙ t')
skip2lProof' t' (consβ t) = consβ (t ∙ t')
skip2lProof' t' (succβ tt t) = succβ (skip2lProof' t' tt) (skip2lProof t' t)

skip2rProof' : ∀ {σ Γ A} {t₁ t₂ : Term Γ σ} → (t' : Term Γ (σ ↝ A)) → t₁ ↠β t₂ → (t' ∙ t₁) ↠β (t' ∙ t₂)
skip2rProof' t' (consβ t) = consβ (t' ∙ t)
skip2rProof' t' (succβ tt t) = succβ (skip2rProof' t' tt) (skip2rProof t' t)

skipthProof' : ∀ {σ Γ A} {t₁ t₂ : Term (σ ∷ Γ) A} → t₁ ↠β t₂ → (Λ t₁) ↠β (Λ t₂)
skipthProof' (consβ t) = consβ (Λ t)
skipthProof' (succβ tt t) = succβ (skipthProof' tt) (skipthProof t)

join : ∀ {σ Γ A} {t₁ t₂ : Term Γ (σ ↝ A)} {p₁ p₂ : Term Γ σ} → t₁ ↠β t₂ → p₁ ↠β p₂ → (t₁ ∙ p₁) ↠β (t₂ ∙ p₂)
join (consβ t) (consβ p) = consβ (t ∙ p) --{!!}
join (consβ t) p = skip2rProof' t p
join t (consβ p) = skip2lProof' p t
join (succβ tt (reduce t rt)) (succβ pp (reduce p rp)) = succβ (succβ (join tt pp) (skip2lProof p t')) (skip2rProof t'' p')
  where
    t' = (reduce t rt)
    p' = (reduce p rp)
    t'' = applyReduction rt

redexLast : ∀ {σ Γ A} {t₁ : Term (σ ∷ Γ) A} {t₂ : Term Γ σ} {t : Term Γ A} → t ↠β ((Λ t₁) ∙ t₂) → t ↠β (applyReduction (this t₁ t₂))
redexLast {σ} {Γ} {A} {t₁} {t₂} (consβ .(Λ t₁ ∙ t₂)) = succβ (consβ (Λ t₁ ∙ t₂)) (reduce (Λ t₁ ∙ t₂) (this t₁ t₂))
redexLast {σ} {Γ} {A} {t₁} {t₂} (succβ y y') = succβ (succβ y y') (reduce (Λ t₁ ∙ t₂) (this t₁ t₂))

-- just "&&" and ","
data _&&_ (A B : Set) : Set where
  _,_ : A → B → A && B


-- ℓ is \ell
data _↠ℓ_ {Γ} : {A : Type} → Term Γ A → Term Γ A → Set where
  consℓ : ∀{A} (a : A ∈ Γ) → (Var a) ↠ℓ (Var a)
  Λℓ : ∀ {σ A} {t₁ t₂ : Term (σ ∷ Γ) A} → t₁ ↠ℓ t₂ → (Λ t₁) ↠ℓ (Λ t₂)
  ∙ℓ : ∀ {σ A} {t₁ t₂ : Term Γ (σ ↝ A)} {p₁ p₂ : Term Γ σ} → t₁ ↠ℓ t₂ → p₁ ↠ℓ p₂ → (t₁ ∙ p₁) ↠ℓ (t₂ ∙ p₂)
  substℓ : ∀ {σ A} {t₁ t₂ : Term (σ ∷ Γ) A} {p₁ p₂ : Term Γ σ} → t₁ ↠ℓ t₂ → p₁ ↠ℓ p₂ → ((Λ t₁) ∙ p₁) ↠ℓ (substitution p₂ t₂)

-- IMHO Λℓ and ∙ℓ should be functions, not constructors

--Λproof : ∀ {σ Γ A} {t₁ t₂ : Term (σ ∷ Γ) A} → t₁ ↠ℓ t₂ → (Λ t₁) ↠ℓ (Λ t₂)
--Λproof (consℓ t) = consℓ (Λ t)
--Λproof (substℓ ) = {!!}

-- 2006 - page 13, lemma 1.4.2 (i)
lemma1 : ∀ {Γ A} {t₁ t₂ : Term Γ A} → t₁ →β t₂ → t₁ ↠ℓ t₂
lemma1 (reduce ((Λ t₁) ∙ t₂) (this .t₁ .t₂)) = {!!} --substℓ (consβ t₁) (consβ t₂)
lemma1 (reduce (t₁ ∙ t₂) (skip2l .t₁ .t₂ r)) = {!!} -- ∙ℓ (lemma1 (reduce t₁ r)) (consℓ t₂)
lemma1 (reduce (t₁ ∙ t₂) (skip2r .t₁ .t₂ r)) = {!!} -- ∙ℓ (consℓ t₁) (lemma1 (reduce t₂ r))
lemma1 (reduce (Λ t) (skipth .t r)) = Λℓ (lemma1 (reduce t r))
lemma1 (reduce (Var _) ())
--lemma1 (Λβ t) = Λℓ (lemma1 t)
--lemma1 (leftβ t t') = ∙ℓ (lemma1 t') (consℓ t)
--lemma1 (rightβ t t') = ∙ℓ (consℓ t) (lemma1 t')

-- 2006 - page 13, lemma 1.4.2 (ii)
lemma2 : ∀ {Γ A} {t₁ t₂ : Term Γ A} → t₁ ↠ℓ t₂ → t₁ ↠β t₂
lemma2 (consℓ t) = {!!} -- consβ t
lemma2 (Λℓ t) = skipthProof' (lemma2 t)
lemma2 (∙ℓ t p) = join (lemma2 t) (lemma2 p)
lemma2 (substℓ t p) = redexLast init
  where
    t₁ = lemma2 t
    p₁ = lemma2 p
    init = join (skipthProof' t₁) p₁

-- 2006 - page 13, lemma 1.4.2 (iii)
lemma3 : ∀ {σ A Γ} {t₁ t₂ : Term (σ ∷ Γ) A} {p₁ p₂ : Term Γ σ} → t₁ ↠ℓ t₂ → p₁ ↠ℓ p₂ → (substitution p₁ t₁) ↠ℓ (substitution p₂ t₂)
lemma3 t p = {!!}