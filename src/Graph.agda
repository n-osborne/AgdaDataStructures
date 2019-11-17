module Graph where

module InductiveGraph where

open import List
open import Product
open import IdentityRelation
open import Function

variable
  N : Set

data Adj N : Set where
  adj : List N → Adj N
  
data Context N : Set where
  context : Adj N → N → Adj N → Context N

data Graph N : Set where
  empty : Graph N
  _&_   : Context N → Graph N → Graph N


gmap : (Context N → Context N) → Graph N → Graph N
gmap f empty = empty
gmap f (c & g) = f c & gmap f g

gmap-id : ∀ (g : Graph N) → gmap id g ≡ id g
gmap-id empty = refl
gmap-id (x & g) = {!!}

swap : Context N → Context N
swap (context l n r) = context l n r

swap-swap-id : ∀ (c : Context N) → (swap ∘ swap) c ≡ c
swap-swap-id c = {!!}

grev : Graph N → Graph N
grev = gmap swap


gmap-fusion : ∀ (f g : Context N → Context N)(gr : Graph N) → ((gmap g) ∘ (gmap f)) gr ≡ gmap (g ∘ f) gr
gmap-fusion g f empty    = refl
gmap-fusion g f (x & gr) = {!!}

grev∘grev-is-id : ∀ (g : Graph N) → (grev ∘ grev) g ≡ id g
grev∘grev-is-id g = {!!}

ufold : {B : Set} → (Context N → B → B) → B → Graph N → B
ufold f b empty = b
ufold f b (c & g) = f c (ufold f b g)

nodes : Graph N → List N
nodes = ufold f []
  where
    f : Context N → List N → List N
    f (context l n r) = n ::_

-- gsuc and gpred need equality on N and a way to handle n not occuring in g
gsucc : Graph N → N → List N
gsucc g n = {!!}

gpred : Graph N → N → List N
gpred g n = {!!}
