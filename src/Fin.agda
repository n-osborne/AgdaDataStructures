module Fin where

open import Nat
open import Bool
data Fin : ℕ → Set where
  fzero : {n : ℕ} → Fin (S n)
  fsuc : {n : ℕ} → Fin n → Fin (S n)

toNat : ∀ {n} -> Fin n -> ℕ
toNat fzero = O
toNat (fsuc f) = S (toNat f)

