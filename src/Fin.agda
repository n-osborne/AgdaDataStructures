module Fin where

open import Nat

data Fin : ℕ → Set where
  fzero : {n : ℕ} → Fin (S n)
  fsuc : {n : ℕ} → Fin n → Fin (S n)

