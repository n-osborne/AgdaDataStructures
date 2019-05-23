module Graph where


open import Data.List
open import Data.Nat
open import Data.Product


Node = ℕ

data Adj (E : Set) : Set where
  mkAdj : E → Node → Adj E


data Context (A E : Set) : Set where
  mkContext : List (Adj E)  → Node → A → List (Adj E) → Context A E

data Graph (A B : Set) : Set where
  Empty : Graph A B
  _&_   : Context A B → Graph A B → Graph A B


