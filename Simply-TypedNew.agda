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

⊆⊹ : ∀ {a} {A : Set a} → (x : List A) → (y : List A) → (x ⊆ (y ⊹ x))
⊆⊹ x [] = ⊆refl x
⊆⊹ x (y ∷ ys) = ⊆add y (⊆⊹ x ys)

∈⊹ : ∀ {a} {A : Set a} {l' : List A} {x : A} → (l : List A) → (x ∈ l') → (x ∈ (l ⊹ l'))
∈⊹ {_} {_} {l'} l x = (⊆⊹ l' l) x

TList = List Type

infixl 5 _∙_
data Term : TList → Type → Set where
  Var : ∀ {A Γ} → A ∈ Γ → Term Γ A
  Λ   : ∀ {A B Γ} → (a : A ∈ Γ) → Term Γ B → Term (Γ - a) (A ↝ B)
  _∙_ : ∀ {A B Γ} → Term Γ (A ↝ B) → Term Γ A → Term Γ B

weaking : ∀ {Γ Γ' A} → Term Γ' A → Term (Γ ⊹ Γ') A
weaking {Γ} {Γ'} (Var y) = Var ((⊆⊹ Γ' Γ) y)
weaking {Γ1} (Λ {_} {_} {_} a y) = {!!} --Λ (∈⊹ Γ1 a) (weaking y)
weaking {Γ} {Γ'} (y ∙ y') = (weaking {Γ} {Γ'} y) ∙ (weaking {Γ} {Γ'} y')

var-substitution : ∀ {A B Γ Γ'} → (a : A ∈ Γ) → Term Γ' A → (B ∈ (Γ ⊹ Γ')) → Term ((Γ - a) ⊹ Γ') B
var-substitution Z tf Z = {!tf!}
var-substitution Z tf (S n) = Var n
var-substitution (S n) tf Z = Var Z
var-substitution (S n) tf (S n') = {!!}

term-substitution : ∀ {A B Γ Γ'} → (a : A ∈ Γ) → Term Γ' A → Term (Γ ⊹ Γ') B → Term ((Γ - a) ⊹ Γ') B
term-substitution a tf tt = {!!}