module Option where

data Option (A : Set) : Set where
  nothing : Option A
  just    : A → Option A
