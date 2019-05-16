module Nat where

open import Bool

data ℕ : Set where
  O : ℕ
  S : ℕ -> ℕ

_+_ : ℕ -> ℕ -> ℕ
O     + m = m
(S n) + m = S (n + m)

_-_ : ℕ → ℕ → ℕ
n     - O     = n
O     - m     = O
(S n) - (S m) = n - m

_*_ : ℕ → ℕ → ℕ
O * _     = O
_ * O     = O
n * (S m) = n + (n * m)

natrec : {C : Set} → C → (ℕ → C → C) → ℕ → C
natrec c f O     = c
natrec c f (S n) = f n (natrec c f n)

_≡_ : ℕ → ℕ → 𝔹
O     ≡ O     = true
(S n) ≡ (S m) = n ≡ m
_     ≡ _     = false

_<_ : ℕ → ℕ → 𝔹
O     < (S n) = true
(S n) < (S m) = n < m
_     < _     = false

_≤_ : ℕ → ℕ → 𝔹
m ≤ n = (m < n) ∨ (m ≡ n)

_>_ : ℕ → ℕ → 𝔹
m > n = ¬ (m ≤ n)

_≥_ : ℕ → ℕ → 𝔹
m ≥ n = ¬ (m < n)

max : ℕ → ℕ → ℕ
max O m = m
max n O = n
max (S n) (S m) = max n m
