module Vector where

open import Nat
open import Product
open import Fin
open import IdentityRelation

open Classical-Definitions

data Vec {n} (A : Set n) : ℕ → Set n where
  []  : Vec A O
  _∷_ : ∀ {n : ℕ} (a : A) (as : Vec A n) → Vec A (S n)

map : {A B : Set} → {n : ℕ} → (A → B) → Vec A n → Vec B n
map f []       = []
map f (x ∷ xs) = (f x) ∷ (map f xs)

foldl : ∀ {A B : Set} {n} → (B → A → B) → B → Vec A n → B
foldl f b []       = b
foldl f b (a ∷ as) = foldl f (f b a) as

foldr : ∀ {A B : Set} {n} → (A → B → B) → B → Vec A n → B
foldr f b []       = b
foldr f b (a ∷ as) = f a (foldr f b as)

zip : {A B : Set} → {n : ℕ} → Vec A n → Vec B n → Vec (Prod A B) n
zip []       []       = []
zip (x ∷ xs) (y ∷ ys) = (x × y) ∷ (zip xs ys)

_++_ : ∀ {a m n} {A : Set a}  → Vec A m → Vec A n → Vec A (n + m)
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

sum : {n : ℕ} → Vec ℕ n → ℕ
sum = foldr _+_ O

addTail : {A : Set} → {n : ℕ} → A → Vec A n → Vec A (S n)
addTail a []       = a ∷ []
addTail a (x ∷ xs) = x ∷ (addTail a xs)

reverse : {A : Set} → {n : ℕ} → Vec A n → Vec A n
reverse []       = []
reverse (a ∷ as) = addTail a (reverse as)

head : {A : Set} → {n : ℕ} → Vec A (S n) → A
head (a ∷ as) = a

_!_ : {n : ℕ}{A : Set} → Vec A n → Fin n → A
[]       ! ()
(x ∷ xs) ! fzero  = x
(x ∷ xs) ! fsuc i = xs ! i

tabulate : {n : ℕ}{A : Set} → (Fin n → A) → Vec A n
tabulate {O}   f = []
tabulate {S n} f = f fzero ∷ tabulate (λ x → f (fsuc x))

-- Exercices from Norell and Chapman Tutorial
-- 2.1
Matrix : Set → ℕ → ℕ → Set
Matrix A n m = Vec (Vec A n) m

vec : {n : ℕ} {A : Set} → A → Vec A n
vec {O} {A} a = []
vec {S n} {A} a = a ∷ vec {n} a

infixl 90 _$_
_$_ : {n : ℕ}{A B : Set} → Vec (A → B) n → Vec A n → Vec B n
_$_ {.O} [] [] = []
_$_ {.(S _)} (f ∷ fs) (x ∷ xs) = f x ∷ fs $ xs

transpose : ∀ {A n m} → Matrix A n m → Matrix A m n
transpose [] = {!!}
transpose (xss ∷ xss₁) = {!!}

-- 2.2 Vector Lookup
lem-!-tab : forall {A n} (f : Fin n -> A)(i : Fin n) ->
                (tabulate f ! i) ≡ (f i)
lem-!-tab f fzero = refl
lem-!-tab f (fsuc i) = {!!}

