module Simply-TypedNew where

open import Data.Bool
open import Data.List
open import Data.String
open import Level
open import ListProofs
open import Data.Empty using (⊥)
open import Data.Unit using (⊤)

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