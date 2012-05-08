-- 2

module Tut where

-- 2.1

data Bool : Set where
  true  : Bool
  false : Bool

not : Bool → Bool
not true = false
not false = true

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

_+_ : Nat → Nat → Nat
zero + m = m
(suc n) + m = suc (n + m)

_*_ : Nat → Nat → Nat
zero * m = zero
(suc n) * m = m + (n * m)

_and_ : Bool → Bool → Bool
true and x = x
false and _ = false

if_then_else_ : { A : Set } → Bool → A → A → A
if true then x else y = x
if false then x else y = y

infixl 60 _*_
infixl 40 _+_
infixr 20 _and_
infix 5 if_then_else_

infixr 40 _::_

data List ( A : Set ) : Set where
  [] : List A
  _::_ : A → List A → List A

-- 2.2

identity : ( A : Set ) → A → A
identity A x = x

zero' : Nat
zero' = identity Nat zero

apply : ( A : Set ) → (B : A → Set ) → (( x : A ) → B x) → (a : A) → B a
apply A B f a = f a

identity2 : (A : Set) → A → A
identity2 = \A x → x

identity3 : (A : Set) → A → A
identity3 = \(A : Set) (x : A) → x

identity4 : (A : Set) → A → A
identity4 = \(A : Set) x → x

-- 2.3

id : {A : Set} → A → A
id x = x

true' : Bool
true' = id true

silly : {A : Set} {x : A} → A
silly {_}{x} = x

false' : Bool
false' = silly {x = false}

one : Nat
one = identity _ (suc zero)

_◯_ : {A : Set} {B : A → Set} {C : (x : A) → B x → Set}
         (f : {x : A} (y : B x) → C x y) (g : (x : A) → B x) (x : A) → C x (g x)
(f ◯ g) x = f(g x)

map : {A B : Set} → (A → B) → List A → List B
map f []        = []
map f (x :: xl) = (f x) :: (map f xl)

_++_ : {A : Set} → List A → List A → List A
[] ++ xl2         = xl2
(x :: xl1) ++ xl2 = x :: (xl1 ++ xl2)

-- 2.4

data Vec (A : Set) : Nat → Set where
  []   : Vec A zero
  _::_ : {n : Nat} → A → Vec A n → Vec A (suc n)

head : {A : Set} {n : Nat} → Vec A (suc n) → A
head (x :: xl) = x

vmap : {A B : Set} {n : Nat} → (A → B) → Vec A n → Vec B n
vmap f []        = []
vmap f (x :: xl) = (f x) :: (vmap f xl)

data Vec2 (A : Set) : Nat → Set where
  nil : Vec2 A zero
  cons : (n : Nat) → A → Vec2 A n → Vec2 A (suc n)

vmap2 : {A B : Set} (n : Nat) → (A → B) → Vec2 A n → Vec2 B n
vmap2 .zero f nil = nil
vmap2 .(suc n) f (cons n x xl) = cons n (f x) (vmap2 n f xl)

data Image_⋑_ { A B : Set } (f : A → B) : B → Set where
  im : (x : A) → Image f ⋑ f x

inv : {A B : Set} (f : A → B) (y : B) → Image f ⋑ y → A
inv f .(f x) (im x) = x

data Fin : Nat → Set where
  fzero : {n : Nat} → Fin (suc n)
  fsuc : {n : Nat} → (i : Fin n) → Fin (suc n)

data Empty : Set where
  empty : Fin zero → Empty