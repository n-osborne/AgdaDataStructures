module Graph where

open import Data.List
open import Data.Nat
open import Data.Bool
open import Data.Product
open import Data.Vec
open import Data.Maybe
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

module AdjList where

  data Node (E : Set) : Set where
    mkNode : E → Node E

  data Adj (E : Set) : Set where
    mkAdj : Node E → List (Node E) → Adj E

  node : {E : Set} → Adj E → Node E
  node (mkAdj n _) = n
  
  adj : {E : Set} → Adj E → List (Node E)
  adj (mkAdj _ l) = l
  
  data Graph (E : Set) : Set where
    mkGraph : List (Adj E) → Graph E

  -- successors : {E : Set} {{_ : Dec E}} → Graph E → Node E → Maybe (List (Node E))
  -- successors (mkGraph []) _      = nothing
  -- successors (mkGraph ((mkAdj (mkNode n₁) l) ∷ xs)) (mkNode n₂) with ⌊ n₁ ≡ n₂ ⌋
  -- ... | true  = just l
  -- ... | false = successors (mkGraph xs) (mkNode n₂)


module AdjListNat where

  data Node : Set where
    mkNode : ℕ → Node

  data Adj : Set where
    mkAdj : Node → List Node → Adj

  data Graph : Set where
    mkGraph : List Adj → Graph

  node : Adj → Node
  node (mkAdj n _) = n

  adj : Adj → List Node
  adj (mkAdj _ l) = l

  val : Node → ℕ
  val (mkNode n) = n

  _ⁿ≡ᵇ_ : Node → Node → Bool
  (mkNode n₁) ⁿ≡ᵇ (mkNode n₂) = n₁ ≡ᵇ n₂
  
  successors :  Graph → Node → (List Node)
  successors (mkGraph []) _      = []
  successors (mkGraph ((mkAdj n₁ l) ∷ xs)) n₂ with n₁ ⁿ≡ᵇ n₂
  ... | true  = l
  ... | false = successors (mkGraph xs) n₂

  predecessors : Graph → Node → List Node
  predecessors (mkGraph []) _    = []
  predecessors (mkGraph ((mkAdj n₁ l) ∷ xs)) n₂ with any (λ n → n₂ ⁿ≡ᵇ n) l
  ... | true  = n₁ ∷ (predecessors (mkGraph xs) n₂)
  ... | false = (predecessors (mkGraph xs) n₂)

module Inductive where
  Node = ℕ
  
  data Adj (E : Set) : Set where
    mkAdj : E → Node → Adj E
  
  data Context (A E : Set) : Set where
    mkContext : List (Adj E)  → Node → A → List (Adj E) → Context A E
  
  data Graph (A B : Set) : Set where
    Empty : Graph A B
    _&_   : Context A B → Graph A B → Graph A B
  

