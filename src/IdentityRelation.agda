module IdentityRelation where

infix 1 _≡_ 
data _≡_ {A : Set}(x : A) : A → Set where
  refl : x ≡ x
