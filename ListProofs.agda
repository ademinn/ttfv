module ListProofs where

open import Level
open import Data.List

-- ≡ is \==
data _≡_ {l : Level} {A : Set l} : A → A → Set l where
  Refl : {a : A} → (a ≡ a)

-- ∈ is \in
infixr 4 _∈_
data _∈_ {a} {A : Set a} : A → List A → Set a where
  Z : ∀ {x xs} → x ∈ (x ∷ xs)
  S : ∀ {x y xs} → (n : x ∈ xs) → x ∈ (y ∷ xs)

-- ⊆ is \sub=
_⊆_ : ∀ {a} {A : Set a} → List A → List A → Set a
xs ⊆ ys = ∀ {x} → x ∈ xs → x ∈ ys

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

-- ⊹ is \+' '
_⊹_ : ∀ {a} {A : Set a} → List A → List A → List A
l1 ⊹ l2 = Data.List._++_ l1 l2
infixr 5 _⊹_
