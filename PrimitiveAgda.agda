-- Date: April 2012
-- Author: Jan Malakhovski
-- For TTFV: http://oxij.org/activity/ttfv/

-- Everything here is in Public Domain.

module PrimitiveAgda where

-- ≡ is \==
-- Martin-Lof equivalence on values.
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

-- Properties.
≡-refl : {A : Set}{a b : A}
       → a ≡ b → b ≡ a
≡-refl refl = refl

≡-trans : {A : Set}{a b c : A}
        → a ≡ b → b ≡ c → a ≡ c
≡-trans refl refl = refl

_~_ : {A : Set}{a b c : A}
    → a ≡ b → b ≡ c → a ≡ c
_~_ = ≡-trans

cong : {A B : Set}{a b : A}
     → (f : A → B) → a ≡ b → f a ≡ f b
cong f refl = refl

-- ⊥ is \bot
-- Empty type.
data ⊥ : Set where

-- Absurd implies anything.
⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

-- ⊤ is \top
-- One element type.
record ⊤ : Set where
  constructor tt

-- Every type could be squashed into the one element type.
⊤-intro : {A : Set} → A → ⊤
⊤-intro _ = tt
  
-- Booleans.
data Bool : Set where
  true false : Bool

-- Magic!
isTrue : Bool -> Set
isTrue false = ⊥
isTrue true = ⊤

-- ℕ is \bn
-- Naturals.
data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

-- ≠ is \ne
-- Not zero
≠zero : ℕ → Bool
≠zero zero = false
≠zero (succ n) = true

---------------------------------------------------------
-- Example usage of the magic.

constifsnd≠zero : (a : ℕ) → (b : ℕ) → { x : isTrue (≠zero b) } → ℕ
constifsnd≠zero a zero {()}
constifsnd≠zero a (succ b) = a 

--------------------------------------------------------

-- ∘ is \o
-- λ is \lambda
-- Most abstract (and scary) way to type a function composition.
_∘_ : {A : Set}{B : A → Set}{C : {x : A} → B x → Set}
    → (f : {x : A} → (y : B x) → C y) → (g : (x : A) → B x) → ((x : A) → C (g x))
f ∘ g = λ x → f (g x)

-- ∘ could be viewed as a proof of transitivity of the implication.
impl-trans : {A B C : Set}
           → (A → B) → (B → C) → (A → C)
impl-trans f g = g ∘ f

-- ¬ is \lnot
-- Logical negation.
¬ : Set → Set
¬ a = a → ⊥

-- If A implies B then not B implies not A.
¬impl : {A B : Set} → (A → B) → (¬ B → ¬ A)
¬impl f ¬B = impl-trans f ¬B

-- Contradiction implies anything.
contradiction : {A B : Set} → A → ¬ A → B
contradiction a ¬a = ⊥-elim (¬a a)

-------------------------------------------

-- Sum of two naturals.
_+_ : ℕ → ℕ → ℕ
_+_ zero a = a
_+_ (succ a) b = succ (a + b)

-- Operations' associativity and priorities to make Agda's parser happy.
infixl 10 _~_
infix 10 _≡_
infixl 20 _+_

-- Properties.
lemma-succ : {x y : ℕ} → x ≡ y → succ x ≡ succ y
lemma-succ refl = refl

lemma-unsucc : {x y : ℕ} → succ x ≡ succ y → x ≡ y
lemma-unsucc refl = refl

assoc : (x y z : ℕ) → x + (y + z) ≡ (x + y) + z
assoc zero y z = refl
assoc (succ x) y z = lemma-succ (assoc x y z)

y=y+0 : (y : ℕ) → y ≡ y + zero
y=y+0 zero = refl
y=y+0 (succ y) = lemma-succ (y=y+0 y)

sy=y+1 : (y : ℕ) → succ y ≡ y + succ zero
sy=y+1 zero = refl
sy=y+1 (succ y) = lemma-succ (sy=y+1 y)

sx+y=x+sy : (x y : ℕ) → succ x + y ≡ x + succ y
sx+y=x+sy zero y = refl
sx+y=x+sy (succ x) y = cong succ (sx+y=x+sy x y)

-- (*) Commutativity.
comm : (x y : ℕ) → x + y ≡ y + x
comm zero y = y=y+0 y
comm (succ x) y = (cong succ (comm x y)) ~ (sx+y=x+sy y x)

-- Define multiplication:
infixl 30 _*_
_*_ : ℕ → ℕ → ℕ
_*_ zero y = zero
_*_ (succ x) y = y + (x * y)

-- (**) Prove its properties:
0=y*0 : (y : ℕ) → zero ≡ y * zero
0=y*0 zero = refl
0=y*0 (succ y) = 0=y*0 y

y=y*1 : (y : ℕ) → y ≡ y * (succ zero)
y=y*1 zero = refl
y=y*1 (succ y) = lemma-succ (y=y*1 y)

_$_ : {a b : Set} → (a → b) → a → b
f $ x = f x
infixr 0 _$_

ldistr : (x y z : ℕ) → (x + y) * z ≡ x * z + y * z
ldistr zero y z = refl
ldistr (succ x) y z = (cong (_+_ z) $ (ldistr x y z)) ~ (assoc z (x * z) (y * z))

assoc* : (x y z : ℕ) → x * (y * z) ≡ (x * y) * z
assoc* zero y z = refl
assoc* (succ x) y z = (cong (_+_ (y * z)) $ (assoc* x y z)) ~ (≡-refl $ (ldistr y (x * y) z))

lemma-plus-z : {x y z : ℕ} → x ≡ y → (z : ℕ) → x + z ≡ y + z
lemma-plus-z refl z = cong ((λ z a → a + z) z) refl

rdistr : (x y z : ℕ) → x * (y + z) ≡ x * y + x * z
rdistr zero y z = refl
rdistr (succ x) y z = (≡-refl $ assoc y z (x * (y + z))) ~ (cong (_+_ y) $ ((((cong (_+_ z) $ (rdistr x y z)) ~ (assoc z (x * y) (x * z))) ~ (lemma-plus-z (comm z (x * y)) (x * z))) ~ (≡-refl $ (assoc (x * y) z (x * z) ))) ) ~ (assoc y (x * y) (z + x * z))

comm* : (x y : ℕ) → x * y ≡ y * x
comm* zero y = 0=y*0 y
comm* (succ x) y = (cong (_+_ y) $ (comm* x y)) ~ (≡-refl $ (rdistr y (succ zero) (x)) ~ lemma-plus-z (≡-refl (y=y*1 y)) (y * x))

-------------------------------------------
-- Emulating type classes.

-- Interface. Almost Haskell's "class" keyword
record Summable (A : Set) : Set where
  field
    _+'_ : A → A → A

-- Haskell: (Summable A) => A -> A -> A
abstractSum : ∀ {A} → (Summable A) → A → A → A
abstractSum s = _+'_ where
  open Summable s
-- But! In Haskell Summable is not just an argument, it is inferenced.

-- Taking Summable A from a context of a call with "instance arguments"
-- available in the recent versions of Agda:
abstractSum' : ∀ {A} → {{s : Summable A}} → A → A → A
abstractSum' {{s}} = _+'_ where
  open Summable s

-- Inferencing with bare hands:

-- Hidden details (not visible in Haskell).
data What : Set where
  bool nat : What

-- Reversable total function.
W : What -> Set
W bool = Bool
W nat = ℕ

-- If you give me a name of a type I'll give you an implementation of the interface.
-- Almost like Haskell's "instance" declaration.
getSummable : (x : What) → Summable (W x)
getSummable bool = record { _+'_ = (λ x y -> x) }
getSummable nat = record { _+'_ = (λ x y -> y) }

-- Magic!
abstractSum'' : {x : What} → W x → W x → W x
abstractSum'' {x} = abstractSum {A = W x} (getSummable x)

-------------------------------------------

-- Maybes (optional values).
data Maybe (A : Set) : Set where
  just : A → Maybe A
  nothing : Maybe A

-- Categorical sum.
data Either (A B : Set) : Set where
  left : A → Either A B
  right : B → Either A B
  
-- ∷ is \::
-- Lists.
data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

length : ∀ {A} → List A → ℕ
length [] = zero
length (a ∷ as) = succ (length as)
  
-- Lists of known length (vectors).
data Vec (A : Set) : ℕ → Set where
  [0] : Vec A zero
  _::_ : {n : ℕ} → A → Vec A n → Vec A (succ n)

head : ∀ {A n} → Vec A (succ n) → A
head (a :: as) = a
  
-- Finite type. Each Fin n has exactly n elements.
data Fin : ℕ → Set where
  fzero : Fin (succ zero)
  fsucc : ∀ {n} → Fin n → Fin (succ n)

-- Get an element from a Vec by its number.
lookup : ∀ {A n} → Fin n → Vec A n → A
lookup fzero (a :: as) = a
lookup (fsucc sn) (a :: as) = a

-- try this:
--test1 = head [0]

list2vec : ∀ {A} → (l : List A) → Vec A (length l)
list2vec [] = [0]
list2vec (a ∷ as) = a :: (list2vec as)

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

fst : ∀ {A B} → A × B → A
fst (a , b) = a

snd : ∀ {A B} → A × B → B
snd (a , b) = b
  
infixl 15 _×_
  
data _<_ : ℕ → ℕ → Set where
  z<s : {n : ℕ} → zero < succ n
  s<s  : {n m : ℕ} → n < m → succ n < succ m

-- ≤ is \le
_≤_ : ℕ → ℕ → Set
a ≤ b = Either (a ≡ b) (a < b)

-- (**) If you give me a list and a proof that its length is less than n
-- I'll give you a tuple (prefix of length n, suffix)
cuthead : ∀ {A} {n : ℕ} → (l : List A) → n ≤ length l → Vec A n × List A
cuthead {n = zero} l p = [0] , l
cuthead {n = succ k} [] (left ())
cuthead {n = succ k} [] (right ())
cuthead {n = succ k} (lf ∷ ls) (left rfl) = (lf :: (fst oldch)) , (snd oldch)
  where oldch = cuthead {n = k} ls (left (lemma-unsucc rfl))
cuthead {n = succ k} (lf ∷ ls) (right (s<s lss)) = (lf :: (fst oldch)), (snd oldch)
  where oldch = cuthead {n = k} ls (right lss)

-- (***) Previous definition is not total (e.g. you can make up any suffix).
-- Define a better one.
-- You may need to define the subtraction with the following property:
--   ∀ a b → a ≤ b → a - b ≡ 0

_-_ : ℕ → ℕ → ℕ
zero - n = zero
n - zero = n
(succ n) - (succ k) = n - k

infixl 20 _-_

n-n=0 : (n : ℕ) → (n - n ≡ zero)
n-n=0 zero = refl
n-n=0 (succ n) = n-n=0 n

a=ba-b=0 : {a b : ℕ} → (a ≡ b) → (a - b ≡ zero)
a=ba-b=0 {a} {.a} refl = n-n=0 a

lemma-sub : ∀ {a b : ℕ} → a ≤ b → a - b ≡ zero
lemma-sub (left rfl) = a=ba-b=0 rfl
lemma-sub (right z<s) = refl
lemma-sub (right (s<s lss)) = lemma-sub (right lss)

n-0=n : (n : ℕ) → n - zero ≡ n
n-0=n zero = refl
n-0=n (succ n) = refl

splitn : ∀ {A} {n : ℕ} → (l : List A) → (n ≤ length l) → Vec A n × Vec A ((length l) - n)
splitn {n = zero} l p = [0] , fst (cuthead {n = length l - zero} l (left (n-0=n (length l))))
splitn {n = succ k} [] (left ())
splitn {n = succ k} [] (right ())
splitn {n = succ k} (lf ∷ ls) (left rfl) = (lf :: (fst oldsn)) , (snd oldsn)
  where oldsn = splitn {n = k} ls (left (lemma-unsucc rfl))
splitn {n = succ k} (lf ∷ ls) (right (s<s lss)) = (lf :: (fst oldsn)) , (snd oldsn)
  where oldsn = splitn {n = k} ls (right lss)