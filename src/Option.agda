module Option where

data Option (A : Set) : Set where
  nothing : Option A
  just    : A → Option A

map : {A B : Set} → (A → B) → Option A → Option B
map f nothing  = nothing
map f (just a) = just (f a)
