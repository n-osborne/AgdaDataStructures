module List where

open import Nat

data List (A : Set) : Set where
  []   : List A
  _::_ : A → List A → List A

map : {A B : Set} → (A → B) → List A → List B
map f []        = []
map f (x :: xs) = f x :: (map f xs)

foldr : {A B : Set} → (A → B → B) → B → List A → B
foldr f b []        = b
foldr f b (x :: xs) = f x (foldr f b xs)

_++_ : {A : Set} → List A → List A → List A
[]        ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

reverse : {A : Set} → List A → List A
reverse []        = []
reverse (x :: xs) = (reverse xs) ++ (x :: [])

reverseAux : {A : Set} → List A → List A → List A
reverseAux [] acc        = acc
reverseAux (x :: xs) acc = reverseAux xs (x :: acc)

reverse' : {A : Set} → List A → List A
reverse' xs = reverseAux xs []

length : {A : Set} → List A → ℕ
length []        = O
length (x :: xs) = S (length xs)
