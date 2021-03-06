module BST where

open import Nat

data Bst (A : Set) : Set where
  leaf : A → Bst A
  node : A → Bst A → Bst A → Bst A

data SizeBst {n} (A : Set n) : ℕ → Set n where
  leaf : A → SizeBst A (S O)
  node : ∀ {n m : ℕ} (a : A) (t1 : SizeBst A n) (t2 : SizeBst A m) → SizeBst A (S (n + m))

data HeightBst {n} (A : Set n) : ℕ → Set n where
  leaf : A → HeightBst A O
  node : ∀ {n m : ℕ} (a : A) (t1 : HeightBst A n) (t2 : HeightBst A m) → HeightBst A (S (max m n)) 
