module DAG where

open import Data.Fin         using (Fin; _<_; _≟_)
open import Data.Nat         using (zero; suc) renaming (ℕ to Nat)
open import Data.List        using (List; map; foldr; _++_; []; _∷_)
open import Data.Product     using (∃-syntax; proj₁)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary  using (Decidable)
open import Data.List.Relation.Unary.Any          using (Any; any)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)


record DAG (n : Nat) : Set where
  field
    edge : (v : Fin n) -> List (∃[ x ] (v < x))
open DAG

next : ∀ {n} -> DAG n -> Fin n -> List (Fin n)
next dg v = map proj₁ (edge dg v)

_∈_ : ∀ {n} -> Fin n -> List (Fin n) -> Set _
v ∈ vs = Any (λ x -> v ≡ x) vs

_∈?_ : ∀ {n} -> Decidable (_∈_ {n})
v ∈? vs = any (λ x -> v ≟ x) vs

mutual
  dfs : ∀ {n} -> Nat -> DAG n -> List (Fin n) -> Fin n -> List (Fin n)
  dfs zero _ acc _ = acc
  dfs (suc gas) dg acc v with v ∈? acc
  dfs (suc gas) dg acc v | yes _ = acc
  dfs (suc gas) dg acc v | no  _ = map-dfs gas dg acc (next dg v)

  map-dfs : ∀ {n} -> Nat -> DAG n -> List (Fin n) -> List (Fin n) -> List (Fin n)
  map-dfs zero _ acc _ = acc
  map-dfs (suc gas) dg acc [] = acc
  map-dfs (suc gas) dg acc (v₁ ∷ vs) = map-dfs gas dg (acc ++ (dfs gas dg acc v₁)) vs
