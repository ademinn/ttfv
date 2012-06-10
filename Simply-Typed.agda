module Simply-Typed where

open import Data.Bool
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

_=t_ : Type → Type → Bool
con y =t con y' = y == y'
con y =t (y' ↝ y0) = false
(y ↝ y') =t con y0 = false
(y ↝ y') =t (y0 ↝ y1) = y =t y0 ∧ y' =t y1

TList = List Type

_=l_ : (xs : TList) → (ys : TList) → Bool
[] =l [] = true
[] =l (x ∷ xs) = false
(x ∷ xs) =l [] = false
(x ∷ xs) =l (x' ∷ xs') = x =t x' ∧ xs =l xs'

ys⊆xs∷ys : (xs : TList) → (ys : TList) → (ys ⊆ (xs ⊹ ys))
ys⊆xs∷ys [] ys = ⊆refl ys
ys⊆xs∷ys (x ∷ xs) ys = ⊆add x (ys⊆xs∷ys xs ys)

-- ∙ is \.
-- ∷ is \::
infixl 5 _∙_
data Term (Γ : TList) : Type → Set where
  Var : ∀ {A} → A ∈ Γ → Term Γ A
  Λ   : ∀ {A B} → Term (A ∷ Γ) B → Term Γ (A ↝ B)
  _∙_ : ∀ {A B} → Term Γ (A ↝ B) → Term Γ A → Term Γ B

data _≡t_ {Γ Γ' : TList} : {A : Type} → Term Γ A → Term Γ' A → Set where
  _≡v_ : ∀ {A} (a : A ∈ Γ) → (a' : A ∈ Γ') → (Var a) ≡t (Var a')
  _≡Λ_ : ∀ {A B} {t₁ : Term (A ∷ Γ) B} {t₂ : Term (A ∷ Γ') B} → t₁ ≡t t₂ → (Λ t₁) ≡t (Λ t₂)

wk : ∀ {Γ Δ A} → (Γ ⊆ Δ) → Term Γ A → Term Δ A
wk θ (Var y) = Var (θ y)
wk θ (y₁ ∙ y₂) = wk θ y₁ ∙ wk θ y₂
wk θ (Λ y) = Λ (wk (⊆cong Refl θ) y)

weaking : ∀ {Γ A B} → Term Γ B → Term (A ∷ Γ) B
weaking {Γ} {A} = wk (xs⊆x∷xs A Γ)

exchange : ∀ {Γ A B C} → Term (A ∷ B ∷ Γ) C → Term (B ∷ A ∷ Γ) C
exchange = wk x∷y∷s⊆y∷x∷s

contraction : ∀ {Γ A B} → Term (A ∷ A ∷ Γ) B → Term (A ∷ Γ) B
contraction = wk (x∈s,x∷s⊆s Z)

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

substitution : ∀ {Γ A C} → Term Γ A → Term (A ∷ Γ) C → Term Γ C
substitution = term-substitution [] _

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

consℓterm : ∀ {Γ A} → (t : Term Γ A) → t ↠ℓ t
consℓterm (Var y) = consℓ y
consℓterm (Λ y) = Λℓ (consℓterm y)
consℓterm (y ∙ y') = ∙ℓ (consℓterm y) (consℓterm y')


-- 2006 - page 13, lemma 1.4.2 (i)
lemma1 : ∀ {Γ A} {t₁ t₂ : Term Γ A} → t₁ →β t₂ → t₁ ↠ℓ t₂
lemma1 (reduce ((Λ t₁) ∙ t₂) (this .t₁ .t₂)) = substℓ (consℓterm t₁) (consℓterm t₂)
lemma1 (reduce (t₁ ∙ t₂) (skip2l .t₁ .t₂ r)) = ∙ℓ (lemma1 (reduce t₁ r)) (consℓterm t₂)
lemma1 (reduce (t₁ ∙ t₂) (skip2r .t₁ .t₂ r)) = ∙ℓ (consℓterm t₁) (lemma1 (reduce t₂ r))
lemma1 (reduce (Λ t) (skipth .t r)) = Λℓ (lemma1 (reduce t r))
lemma1 (reduce (Var _) ())
--lemma1 (Λβ t) = Λℓ (lemma1 t)
--lemma1 (leftβ t t') = ∙ℓ (lemma1 t') (consℓ t)
--lemma1 (rightβ t t') = ∙ℓ (consℓ t) (lemma1 t')

-- 2006 - page 13, lemma 1.4.2 (ii)
lemma2 : ∀ {Γ A} {t₁ t₂ : Term Γ A} → t₁ ↠ℓ t₂ → t₁ ↠β t₂
lemma2 (consℓ t) = consβ (Var t)
lemma2 (Λℓ t) = skipthProof' (lemma2 t)
lemma2 (∙ℓ t p) = join (lemma2 t) (lemma2 p)
lemma2 (substℓ t p) = redexLast init
  where
    t₁ = lemma2 t
    p₁ = lemma2 p
    init = join (skipthProof' t₁) p₁

ℓexchange : ∀ {A B C Γ} {t₁ t₂ : Term (A ∷ B ∷ Γ) C}
  → t₁ ↠ℓ t₂ → (exchange t₁) ↠ℓ (exchange t₂)
ℓexchange (consℓ a) = consℓterm (exchange (Var a))
ℓexchange (Λℓ y) = {!!}
ℓexchange (∙ℓ y y') = {!!}
ℓexchange (substℓ y y') = {!!}

ℓweaking : ∀ {A' Γ} {t₁ t₂ : Term Γ A'}
  → (σ : Type) → t₁ ↠ℓ t₂ → (weaking {A = σ} t₁) ↠ℓ (weaking {A = σ} t₂)
ℓweaking σ (consℓ a) = consℓ (S a)
ℓweaking σ (Λℓ y) = {!!}
ℓweaking σ (∙ℓ y y') = {!!}
ℓweaking σ (substℓ y y') = {!!}

ℓfirst : ∀ {σ Γ} {t₁ t₂ : Term Γ σ} → t₁ ↠ℓ t₂ → Term Γ σ
ℓfirst (consℓ a) = Var a
ℓfirst (Λℓ y) = Λ (ℓfirst y)
ℓfirst (∙ℓ y y') = ℓfirst y ∙ ℓfirst y'
ℓfirst (substℓ y y') = Λ (ℓfirst y) ∙ ℓfirst y'

--pickup : ∀ {} (Term )

-- 2006 - page 13, lemma 1.4.2 (iii)
lemma3 : ∀ {σ A Γ} {t₁ t₂ : Term (σ ∷ Γ) A} {p₁ p₂ : Term Γ σ} → t₁ ↠ℓ t₂ → p₁ ↠ℓ p₂ → (substitution p₁ t₁) ↠ℓ (substitution p₂ t₂)
lemma3 (consℓ Z) p = p
lemma3 (consℓ (S n)) p = consℓ n
lemma3 {σ = σ1} {Γ = Γ} (Λℓ {A} {B} y) p = Λℓ (consℓterm (term-substitution [ A ] Γ (ℓfirst {σ1} {Γ} p) (ℓfirst {!!})))
lemma3 (∙ℓ y y') p = {!!}
lemma3 (substℓ y y') p = {!!}

tlemma3 : ∀ {σ A Γ Γ'} {t₁ t₂ : Term (Γ ⊹ [ σ ] ⊹ Γ') A} {p₁ p₂ : Term Γ' σ}
  → t₁ ↠ℓ t₂ → p₁ ↠ℓ p₂ → (term-substitution Γ Γ' p₁ t₁) ↠ℓ (term-substitution Γ Γ' p₂ t₂)
tlemma3 {Γ = []} (consℓ Z) pp = pp
tlemma3 {Γ = σ' ∷ Γ'} (consℓ Z) pp = consℓ Z
tlemma3 {Γ = []} (consℓ (S n)) pp = consℓ n
tlemma3 {Γ = σ' ∷ Γ1} (consℓ (S n)) pp = {!ℓweaking σ' (tlemma3 {Γ = Γ1} (consℓ n) pp)!}
tlemma3 (Λℓ y) pp = {!!}
tlemma3 (∙ℓ y y') pp = {!!}
tlemma3 (substℓ y y') pp = {!!}

_* : ∀ {Γ A} → Term Γ A → Term Γ A
(Var a)* = Var a
(Λ y)* = Λ (y *)
((Λ y) ∙ y')* = substitution (y' *) (y *)
(y ∙ y') * = (y *) ∙ (y' *)

-- 2006 - page 14, lemma 1.4.4
lemma4 : ∀ {Γ A} {t₁ t₂ : Term Γ A} → t₁ ↠ℓ t₂ → t₂ ↠ℓ (t₁ *)
lemma4 (consℓ t) = consℓ t
lemma4 (Λℓ t) = Λℓ (lemma4 t)
lemma4 (∙ℓ (Λℓ t) p) = substℓ (lemma4 t) (lemma4 p)
lemma4 (∙ℓ (consℓ a) p) = ∙ℓ (lemma4 (consℓ a)) (lemma4 p)
lemma4 (∙ℓ (∙ℓ y y') p) = ∙ℓ (lemma4 (∙ℓ y y')) (lemma4 p)
lemma4 (∙ℓ (substℓ y y') p) = ∙ℓ (lemma4 (substℓ y y')) (lemma4 p)
lemma4 (substℓ t p) = {!!}
