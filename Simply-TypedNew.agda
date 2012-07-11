module Simply-TypedNew where

open import Data.Bool
open import Data.List
open import Data.String
open import Level
open import ListProofs
open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Data.Product

infixr 5 _↝_
data Type : Set where
  con : String → Type
  _↝_ : Type → Type → Type

_-_ : ∀ {a} {A : Set a} {x : A} → (l : List A) → (x ∈ l) → List A
(x ∷ xs) - Z = xs
(x ∷ xs) - (S n) = x ∷ (xs - n)
[] - ()

data _≣_ {a} {A : Set a} : List A → List A → Set a where
  LRefl : (l1 l2 : List A) → (l1 ⊆ l2) → (l2 ⊆ l1) → l1 ≣ l2

_≡e_ : ∀ {a} {A : Set a} {x y : A} {l : List A} → (x ∈ l) → (y ∈ l) → Bool
Z ≡e Z = true
Z ≡e S n = false
S n ≡e Z = false
S n ≡e S n' = n ≡e n'

--data NEq {a} {A : Set a} : {l : List A} {x y : A} → (x ∈ l) → (y ∈ l) → Set where
--  left : {xs : List A} {x : A} → (t : x ∈ xs) → NEq {l = xs} (S t) (Z)


 
--_+_ : ∀ {a} {A : Set a} → (l : List A) → (x : A) → List A

⊆⊹ : ∀ {a} {A : Set a} → (x : List A) → (y : List A) → (x ⊆ (y ⊹ x))
⊆⊹ x [] = ⊆refl x
⊆⊹ x (y ∷ ys) = ⊆add y (⊆⊹ x ys)

∈⊹ : ∀ {a} {A : Set a} {l l' : List A} {x : A} → (l' ⊆ l) → (x ∈ l') → (x ∈ l)
∈⊹ θ a = θ a

x∈xs,x∈y∷xs : ∀ {l} {x y : Set l} {xs} → (x ∈ xs) → (x ∈ y ∷ xs)
x∈xs,x∈y∷xs Z = S Z
x∈xs,x∈y∷xs (S n) = S (x∈xs,x∈y∷xs n)

+a-aT : ∀ {l} {A x : Set l} {Γ} → (a : A ∈ Γ) → (x ∈ Γ) → (x ∈ (A ∷ (Γ - a)))
+a-aT n1 n2 = {!!}

+a-a : ∀ {l} {A : Set l} {Γ} → (a : A ∈ Γ) → (Γ ⊆ (A ∷ (Γ - a)))
+a-a n = +a-aT n

foo : ∀ {a} {A : Set a} {l : List A} {x₁ x₂ : A}
  → (t₁ : x₁ ∈ l) → (t₂ : x₂ ∈ l) → ((t₁ ≡e t₂) ≡ false) → (x₂ ∈ (l - t₁))
foo Z Z ()
foo Z (S n) x = n
foo (S n) Z x = Z
foo (S n) (S n') x = S (foo n n' x)

∈add' : ∀ {a} {A : Set a} {l l' : List A} {x : A} → (p : x ∈ l') → ((l' - p) ⊆ l) → (x ∈ (x ∷ l)) → (l' ⊆ (x ∷ l))
∈add' Z θ head Z = head
∈add' Z θ head (S n) = S (θ n)
∈add' (S n) θ head Z = S (θ Z)
∈add' (S n) θ head (S n') = ∈add' n (λ {x} z → θ (S z)) head n' -- {!S (∈add' n θ head n')!}

∈add : ∀ {a} {A : Set a} {l l' : List A} {x : A} → (p : x ∈ l') → ((l' - p) ⊆ l) → (l' ⊆ (x ∷ l))
∈add p θ = ∈add' p θ Z -- {!λ x → if (x ≡e p) then Z else S(θ x)!}

TList = List Type

infixl 5 _∙_
data Term : TList → Type → Set where
  Var : ∀ {A Γ} → A ∈ Γ → Term Γ A
  Λ   : ∀ {A B Γ} → (a : A ∈ Γ) → Term Γ B → Term (Γ - a) (A ↝ B)
  _∙_ : ∀ {A B Γ} → Term Γ (A ↝ B) → Term Γ A → Term Γ B

--perm : ∀ {Γ Γ' A} → Term Γ A → (Γ ≣ Γ') → Term Γ' A
--perm t r = {!!}

weaking : ∀ {Γ Γ' A} → (Γ' ⊆ Γ) → Term Γ' A → Term Γ A
weaking θ (Var y) = Var (θ y)
weaking θ (Λ Z y) = Λ Z (weaking (∈add Z θ) y)
weaking θ (Λ (S n) y) = Λ Z (weaking (∈add (S n) θ) y)
--weaking {Γ1} θ (Λ {A} {B} a y) = {!Λ Z (weaking{A ∷ Γ1} (xs⊆x∷xs A Γ1) y)!} --Λ (∈⊹ Γ1 a) (weaking y)
weaking θ (y ∙ y') = (weaking θ y) ∙ (weaking θ y')

var-subst : ∀ {A B Γ Γ'} → (a : A ∈ Γ) → Term Γ' A → (B ∈ (Γ ⊹ Γ')) → Term ((Γ - a) ⊹ Γ') B
var-subst {A} {.A} {.A ∷ []} Z tf Z = tf
var-subst {A} {.A} {.A ∷ x ∷ xs} Z tf Z = weaking (λ {x'} → S) (var-subst {A} {A} {A ∷ xs} Z tf Z)
var-subst Z tf (S n) = Var n
var-subst (S n) tf Z = Var Z
var-subst (S n) tf (S n') = weaking (λ {x} → S) (var-subst n tf n')

term-subst : ∀ {A B Γ Γ'} → (a : A ∈ Γ) → Term Γ' A → Term (Γ ⊹ Γ') B → Term ((Γ - a) ⊹ Γ') B
term-subst {A} {con y} n tf (Var y') = var-subst {A} {con y} n tf y'
term-subst {A} {con y} n tf (y0 ∙ y1) = term-subst n tf y0 ∙ term-subst n tf y1
term-subst {A} {y1 ↝ y2} {[]} () tf tt
-- Here I REALLY NEED to pattern-match by tt! Or… mm… proof of tt is made by Λ constructor (because, in fact, we should substitute in {!!} second arg of Λ, check it)
term-subst {A} {y1 ↝ y2} {x ∷ xs} {Γ'} n tf tt = Λ {y1} {y2} {y1 ∷ (((x ∷ xs) - n) ⊹ Γ')} Z (term-subst {A} {y2} {y1 ∷ x ∷ xs} {Γ'} (S n) tf {!!})
--term-subst {A} {y ↝ y'} Z tf tt = Λ {!!} (term-subst Z tf {!!})
--term-subst {A} {y ↝ y'} (S n) tf tt = Λ {!!} (term-subst (S n) tf {!!})

subst : ∀ {A Γ σ} (a : A ∈ Γ) → Term (Γ - a) A → Term Γ σ → Term (Γ - a) σ
subst {A} {Γ} {σ} a t1 t2 = term-subst {A} {σ} {[ A ]} {Γ - a} Z t1 (weaking (λ {x} b → {!+a-a ? ?!}) t2)

data Redex : {Γ : TList} {A : Type} → (Term Γ A) → Set where
  this   : ∀ {A σ Γ} (a : σ ∈ Γ) → (t₁ : Term Γ A) → (t₂ : Term (Γ - a) σ) → Redex ((Λ a t₁) ∙ t₂)
  skip2l : ∀ {A σ Γ} (t₁ : Term Γ (σ ↝ A)) → (t₂ : Term Γ σ) → Redex t₁ → Redex (t₁ ∙ t₂)
  skip2r : ∀ {A σ Γ} (t₁ : Term Γ (σ ↝ A)) → (t₂ : Term Γ σ) → Redex t₂ → Redex (t₁ ∙ t₂)
  skipth : ∀ {A σ Γ} (a : σ ∈ Γ) → (t : Term Γ A) → Redex t → Redex (Λ a t)

applyReduction : ∀ {A} {Γ} {t : Term Γ A} → Redex t → Term Γ A
applyReduction (this a t₁ t₂) = subst a t₂ t₁
applyReduction (skip2l t₁ t₂ y) = (applyReduction y) ∙ t₂
applyReduction (skip2r t₁ t₂ y) = t₁ ∙ (applyReduction y)
applyReduction (skipth a t y) = Λ a (applyReduction y)

data _→β_ {Γ} : {A : Type} → Term Γ A → Term Γ A → Set where
  reduce : ∀ {A} (t : Term Γ A) → (r : Redex t) → t →β (applyReduction r)

skip2lProof : ∀ {σ Γ A} {t₁ t₂ : Term Γ (σ ↝ A)} → (t' : Term Γ σ) → t₁ →β t₂ → (t₁ ∙ t') →β (t₂ ∙ t')
skip2lProof t' (reduce t r) = reduce (t ∙ t') (skip2l t t' r)

skip2rProof : ∀ {σ Γ A} {t₁ t₂ : Term Γ σ} → (t' : Term Γ (σ ↝ A)) → t₁ →β t₂ → (t' ∙ t₁) →β (t' ∙ t₂)
skip2rProof t' (reduce t r) = reduce (t' ∙ t) (skip2r t' t r)

skipthProof : ∀ {σ Γ A} {a : σ ∈ Γ} {t₁ t₂ : Term Γ A} → t₁ →β t₂ → (Λ a t₁) →β (Λ a t₂)
skipthProof {a = a} (reduce t r) = reduce (Λ a t) (skipth a t r)

data _↠β_ {Γ A} : Term Γ A → Term Γ A → Set where
  consβ : (t : Term Γ A) → t ↠β t
  succβ : ∀ {t₁ t₂ t₃} → t₁ ↠β t₂ → t₂ →β t₃ → t₁ ↠β t₃

skip2lProof' : ∀ {σ Γ A} {t₁ t₂ : Term Γ (σ ↝ A)} → (t' : Term Γ σ) → t₁ ↠β t₂ → (t₁ ∙ t') ↠β (t₂ ∙ t')
skip2lProof' t' (consβ t) = consβ (t ∙ t')
skip2lProof' t' (succβ tt t) = succβ (skip2lProof' t' tt) (skip2lProof t' t)

skip2rProof' : ∀ {σ Γ A} {t₁ t₂ : Term Γ σ} → (t' : Term Γ (σ ↝ A)) → t₁ ↠β t₂ → (t' ∙ t₁) ↠β (t' ∙ t₂)
skip2rProof' t' (consβ t) = consβ (t' ∙ t)
skip2rProof' t' (succβ tt t) = succβ (skip2rProof' t' tt) (skip2rProof t' t)

skipthProof' : ∀ {σ Γ A} {a : σ ∈ Γ} {t₁ t₂ : Term Γ A} → t₁ ↠β t₂ → (Λ a t₁) ↠β (Λ a t₂)
skipthProof' {a = a} (consβ t) = consβ (Λ a t)
skipthProof' (succβ tt t) = succβ (skipthProof' tt) (skipthProof t)

join : ∀ {σ Γ A} {t₁ t₂ : Term Γ (σ ↝ A)} {p₁ p₂ : Term Γ σ} → t₁ ↠β t₂ → p₁ ↠β p₂ → (t₁ ∙ p₁) ↠β (t₂ ∙ p₂)
join (consβ t) (consβ p) = consβ (t ∙ p)
join (consβ t) p = skip2rProof' t p
join t (consβ p) = skip2lProof' p t
join (succβ tt (reduce t rt)) (succβ pp (reduce p rp)) = succβ (succβ (join tt pp) (skip2lProof p t')) (skip2rProof t'' p')
  where
    t' = (reduce t rt)
    p' = (reduce p rp)
    t'' = applyReduction rt

redexLast : ∀ {σ Γ A} {a : σ ∈ Γ} {t₁ : Term Γ A} {t₂ : Term (Γ - a) σ} {t : Term (Γ - a) A} → t ↠β ((Λ a t₁) ∙ t₂) → t ↠β (applyReduction (this a t₁ t₂))
redexLast {σ} {Γ} {A} {a} {t₁} {t₂} (consβ .(Λ a t₁ ∙ t₂)) = succβ (consβ (Λ a t₁ ∙ t₂)) (reduce (Λ a t₁ ∙ t₂) (this a t₁ t₂))
redexLast {σ} {Γ} {A} {a} {t₁} {t₂} (succβ y y') = succβ (succβ y y') (reduce (Λ a t₁ ∙ t₂) (this a t₁ t₂))

β-trans : ∀ {Γ A} {t1 t2 t3 : Term Γ A} → (t1 ↠β t2) → (t2 ↠β t3) → (t1 ↠β t3)
β-trans {Γ} {A} {t1} {.t3} {.t3} a (consβ t3) = a
β-trans a (succβ y y') = succβ (β-trans a y) y'

data _↠ℓ_ : ∀ {Γ} {A : Type} → Term Γ A → Term Γ A → Set where
  consℓ : ∀ {A Γ} (a : A ∈ Γ) → (Var a) ↠ℓ (Var a)
  Λℓ : ∀ {σ A Γ} {a : σ ∈ Γ} {t₁ t₂ : Term Γ A} → t₁ ↠ℓ t₂ → (Λ a t₁) ↠ℓ (Λ a t₂)
  ∙ℓ : ∀ {σ A Γ} {t₁ t₂ : Term Γ (σ ↝ A)} {p₁ p₂ : Term Γ σ} → t₁ ↠ℓ t₂ → p₁ ↠ℓ p₂ → (t₁ ∙ p₁) ↠ℓ (t₂ ∙ p₂)
  substℓ : ∀ {σ A Γ} {a : σ ∈ Γ} {t₁ t₂ : Term Γ A} {p₁ p₂ : Term (Γ - a) σ} → t₁ ↠ℓ t₂ → p₁ ↠ℓ p₂ → ((Λ a t₁) ∙ p₁) ↠ℓ (subst a p₂ t₂)

consℓterm : ∀ {Γ A} → (t : Term Γ A) → t ↠ℓ t
consℓterm (Var y) = consℓ y
consℓterm (Λ a y) = Λℓ (consℓterm y)
consℓterm (y ∙ y') = ∙ℓ (consℓterm y) (consℓterm y')

-- 2006 - page 13, lemma 1.4.2 (i)
lemma1 : ∀ {Γ A} {t₁ t₂ : Term Γ A} → t₁ →β t₂ → t₁ ↠ℓ t₂
lemma1 {Γ} {A} {Var y} (reduce .(Var y) ())
lemma1 (reduce (Λ a y) (skipth .a .y y')) = Λℓ (lemma1 (reduce y y'))
lemma1 (reduce (Λ a t₁ ∙ y') (this .a .t₁ .y')) = substℓ (consℓterm t₁) (consℓterm y')
lemma1 {Γ} {A} {y ∙ y'} (reduce .(y ∙ y') (skip2l .y .y' y0)) = ∙ℓ (lemma1 (reduce y y0)) (consℓterm y')
lemma1 {Γ} {A} {y ∙ y'} (reduce .(y ∙ y') (skip2r .y .y' y0)) = ∙ℓ (consℓterm y) (lemma1 (reduce y' y0))

-- 2006 - page 13, lemma 1.4.2 (ii)
lemma2 : ∀ {Γ A} {t₁ t₂ : Term Γ A} → t₁ ↠ℓ t₂ → t₁ ↠β t₂
lemma2 (consℓ a) = consβ (Var a)
lemma2 (Λℓ y) = skipthProof' (lemma2 y)
lemma2 (∙ℓ y y') = join (lemma2 y) (lemma2 y')
lemma2 (substℓ y y') = redexLast (join (skipthProof' (lemma2 y)) (lemma2 y'))

-- 2006 - page 13, lemma 1.4.2 (iii)
lemma3 : ∀ {σ A Γ} {a : σ ∈ Γ} {t₁ t₂ : Term Γ A} {p₁ p₂ : Term (Γ - a) σ} → t₁ ↠ℓ t₂ → p₁ ↠ℓ p₂ → (subst a p₁ t₁) ↠ℓ (subst a p₂ t₂)
lemma3 t p = {!!}

_* : ∀ {Γ A} → Term Γ A → Term Γ A
Var y * = Var y
Λ a y * = Λ a (y *)
((Λ a y) ∙ y') * = subst a (y' *) (y *)
(y ∙ y') * = (y *) ∙ (y' *)

lemma4 : ∀ {Γ A} {t₁ t₂ : Term Γ A} → t₁ ↠ℓ t₂ → t₂ ↠ℓ (t₁ *)
lemma4 (consℓ a) = consℓ a
lemma4 (Λℓ y) = Λℓ (lemma4 y)
lemma4 (∙ℓ (consℓ a) y') = ∙ℓ (lemma4 (consℓ a)) (lemma4 y')
lemma4 (∙ℓ (Λℓ y) y') = substℓ (lemma4 y) (lemma4 y')
lemma4 (∙ℓ (∙ℓ y y') y0) = ∙ℓ (lemma4 (∙ℓ y y')) (lemma4 y0)
lemma4 (∙ℓ (substℓ y y') y0) = ∙ℓ (lemma4 (substℓ y y')) (lemma4 y0)
lemma4 (substℓ y y') = lemma3 (lemma4 y) (lemma4 y')

ℓ-trans : ∀ {Γ A} {t₁ t₂ t₃ : Term Γ A} → t₁ ↠ℓ t₂ → t₂ ↠ℓ t₃ → t₁ ↠ℓ t₃
ℓ-trans (consℓ a) b = b
ℓ-trans (Λℓ y) (Λℓ y') = Λℓ (ℓ-trans y y')
ℓ-trans (∙ℓ y y') (∙ℓ y0 y1) = ∙ℓ (ℓ-trans y y0) (ℓ-trans y' y1)
ℓ-trans (∙ℓ y y') (substℓ y0 y1) = {!!}
ℓ-trans (substℓ y y') b = {!!}

conv↠β↠ℓ : ∀ {Γ A} {t1 t2 : Term Γ A} → t1 ↠β t2 → t1 ↠ℓ t2
conv↠β↠ℓ {Γ} {A} {.t2} {t2} (consβ .t2) = consℓterm t2
conv↠β↠ℓ (succβ y y') = ℓ-trans (conv↠β↠ℓ y) (lemma1 y')

preCR : ∀ {Γ A} {t t₁ : Term Γ A} → t ↠β t₁ → t₁ ↠β t *
preCR {Γ} {A} {.t₁} {t₁} (consβ .t₁) = lemma2 (lemma4 (consℓterm t₁))
preCR (succβ y y') = lemma2 (lemma4 (ℓ-trans (conv↠β↠ℓ y) (lemma1 y')))

CR : ∀ {Γ A} {t t₁ t₂ : Term Γ A} → t ↠β t₁ → t ↠β t₂ → ∃ (λ r → ((t₁ ↠β r) × (t₂ ↠β r)))
CR {t = t} b1 b2 = t * ,(preCR b1 , preCR b2)