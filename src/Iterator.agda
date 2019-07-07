module Iterator where

open import List
open import Bool
open import TypeClasses

open Eq {{...}} public

record Iterator (A : Set) : Set where
  constructor _,_
  field
    stack₁ : List A
    stack₂ : List A

previous : {A : Set} → Iterator A → Iterator A
previous ((x :: xs) , l) = (xs , (x :: l))
previous i = i

next : {A : Set} → Iterator A → Iterator A
next (xs , (y :: ys)) = ((y :: xs) , ys)
next i = i

elemAfter : {A : Set} ⦃ eqA : Eq A ⦄ → A → Iterator A → 𝔹
elemAfter a (_ , l) = elem a l

elemBefore : {A : Set} ⦃ eqA : Eq A ⦄ → A → Iterator A → 𝔹
elemBefore a (l , _) = elem a l
