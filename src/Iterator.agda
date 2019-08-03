module Iterator (A : Set) where

open import List
open import Bool
open import Option
open import TypeClasses

open Eq {{...}} public

record Iterator : Set where
  constructor _,_,_
  field
    stack₁ : List A
    item   : A
    stack₂ : List A

prev : Iterator → Iterator
prev a@([] , _ , _) = a
prev ((x :: xs) , i , l) = (xs , x , (i :: l))

next : Iterator → Iterator
next a@(_ , _ , []) = a
next (l , i , (x :: xs)) = ((i :: l) , x , xs)

read : Iterator → A
read (_ , v , _) = v

backTo : ⦃ eqA : Eq A ⦄ → Iterator → A → Iterator
backTo a@([] , _ , _) _ = a
backTo a@(_ , i , _) v with i v
... | true  = a
... | false = backTo (prev a) v

-- elemAfter : ⦃ eqA : Eq A ⦄ → A → Iterator → 𝔹
-- elemAfter a (_ , l) = elem a l

-- elemBefore : ⦃ eqA : Eq A ⦄ → A → Iterator → 𝔹
-- elemBefore a (l , _) = elem a l

-- goBackTo : {A : Set} ⦃ eqA : Eq A ⦄ → A → Iterator A → Iterator A
-- goBackTo a (s₁ , s₂) = f a s₁ s₂
--   where
--     f : {A : Set} ⦃ eqA : Eq A ⦄ → A → List A → List A → Iterator A
--     f _ [] s        = ([] , s)
--     f a (x :: xs) s = if (a == x) then (xs , (x :: s)) else (f xs (x :: s))
