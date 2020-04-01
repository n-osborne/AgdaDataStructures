module List where

open import Nat
open Nat.Classical-Definitions
open import Bool
open import TypeClasses

open Eq {{...}} public

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

elem : {A : Set} ⦃ eqA : Eq A ⦄ → A → List A → 𝔹
elem _ [] = false
elem a (x :: xs) = (a == x) ∨ (elem a xs)

module lookup-correct-by-construction where
  -- from Ulf Norell and James Chapman "Dependently Typed Programming in Agda"

  -- membership proof (a list (tl, tl,..., hd))
  data _∈_ {A : Set}(x : A) : List A -> Set where
    hd : ∀ {xs}   -> x ∈ (x :: xs)
    tl : ∀ {y xs} -> x ∈ xs -> x ∈ (y :: xs)

  -- index use _∈_ to compute the index of an element in a list
  -- given the membership proof (so we need neither the list not the element
  index : ∀ {A}{x : A}{xs} -> x ∈ xs -> ℕ
  index hd = O
  index (tl p) = S (index p)
  
  -- view data structure on n : either inside the list or outside
  data Lookup {A : Set}(xs : List A) : ℕ -> Set where
    -- inside exhibit the element at index n and the membership proof
    inside  : (x : A) -> (p : x ∈ xs) -> Lookup xs (index p)
    -- outside exhibit the index overflow
    outside : (m : ℕ) -> Lookup xs (m + length xs)
  
  -- view function for Lookup
  -- given a list and an index, exhibit the corresponding Lookup
  -- that is the proof whether it is inside or outside
  _!_ : {A : Set}(xs : List A)(n : ℕ) -> Lookup xs n
  -- the base case when the list is empty
  []        ! n  = outside n
  -- the base case when we arrive at the index
  (x :: xs) ! O  = inside x hd
  -- recursive cases on the list
  (x :: xs) ! S n with xs ! n
  (x :: xs) ! S .(index p)       | inside y p = inside y (tl p)
  (x :: xs) ! S .(m + length xs) | outside m  = outside m

