module DiGraph where

open import Data.Fin using (Fin; _≟_)
open import Data.Nat using (zero; suc) renaming (ℕ to Nat)
open import Data.List using (List; []; _∷_; _++_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary  using (Decidable)
open import Data.List.Relation.Unary.Any          using (Any; any)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- we'll need decidability of membership on List (Fin n)
_∈_ : ∀ {n} -> Fin n -> List (Fin n) -> Set _
v ∈ vs = Any (λ x -> v ≡ x) vs

_∈?_ : ∀ {n} -> Decidable (_∈_ {n})
v ∈? vs = any (λ x -> v ≟ x) vs

record DiGraph (n : Nat) : Set where
  field
    next : Fin n -> List (Fin n)
open DiGraph

mutual
  dfs : ∀ {n} -> Nat -> DiGraph n -> List (Fin n) -> Fin n -> List (Fin n)
  dfs zero dg acc v = acc
  dfs (suc gas) dg acc v with v ∈? acc
  dfs (suc gas) dg acc v | yes _ = acc
  dfs (suc gas) dg acc v | no  _ = dfs-aux gas dg acc (next dg v)

  dfs-aux : ∀ {n} -> Nat -> DiGraph n -> List (Fin n) -> List (Fin n) -> List (Fin n)
  dfs-aux zero dg acc vs            = acc
  dfs-aux (suc gas) dg acc []       = acc
  dfs-aux (suc gas) dg acc (v ∷ vs) = dfs-aux (suc gas) dg (acc ++ dfs gas dg acc v) vs
  

