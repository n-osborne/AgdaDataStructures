module DAG where

open import Data.Fin         using (Fin; _<_; _≟_)
open import Data.Nat         using (zero; suc) renaming (ℕ to Nat)
open import Data.List        using (List; map; foldr; _++_; []; _∷_)
open import Data.Product     using (∃-syntax; proj₁)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary  using (Decidable)
open import Data.List.Relation.Unary.Any          using (Any; any)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- we'll need decidability of membership on List (Fin n)
_∈_ : ∀ {n} -> Fin n -> List (Fin n) -> Set _
v ∈ vs = Any (λ x -> v ≡ x) vs

_∈?_ : ∀ {n} -> Decidable (_∈_ {n})
v ∈? vs = any (λ x -> v ≟ x) vs

-- A Dag is parametrized by the number of Vertices
-- A Vertex is then a Fin n
record DAG (n : Nat) : Set where
  field
    -- an egde from v₁ to v₂ is a proof that v₁ < v₂
    -- hence, we won't have cycle
    edges : (v : Fin n) -> List (∃[ x ] (v < x))
open DAG

-- the function next computes the list of the adjecent vertices
next : ∀ {n} -> DAG n -> Fin n -> List (Fin n)
next dg v = map proj₁ (edges dg v)

-- depth-first search is define by mutual recursion with the search on
-- all the adjacent vertices
mutual
  dfs : ∀ {n} -> Nat -> DAG n -> List (Fin n) -> Fin n -> List (Fin n)
  dfs zero _ acc _ = acc
  dfs (suc gas) dg acc v with v ∈? acc
  dfs (suc gas) dg acc v | yes _ = acc
  dfs (suc gas) dg acc v | no  _ = map-dfs gas dg acc (next dg v)

  map-dfs : ∀ {n} -> Nat -> DAG n -> List (Fin n) -> List (Fin n) -> List (Fin n)
  map-dfs zero _ acc _ = acc
  map-dfs (suc gas) dg acc [] = acc
  map-dfs (suc gas) dg acc (v₁ ∷ vs) = map-dfs (suc gas) dg (acc ++ (dfs gas dg acc v₁)) vs
