module Order where

open import Nat
open import Relation.Binary.PropositionalEquality

data _≤_ : ℕ → ℕ → Set where
  leq-zero : {n : ℕ} → O ≤ n
  leq-succ : {n m : ℕ} → n ≤ m → S n ≤ S m

-- transitivity
leq-trans : {m n o : ℕ} → m ≤ n → n ≤ o → m ≤ o
leq-trans leq-zero _                    = leq-zero
leq-trans (leq-succ m≤n) (leq-succ n≤o) = leq-succ (leq-trans m≤n n≤o)

-- reflexivity
leq-refl : {n : ℕ} → n ≤ n
leq-refl {O}   = leq-zero
leq-refl {S n} = leq-succ (leq-refl {n})

-- anti-symmetry
leq-anti : {m n : ℕ} → m ≤ n → n ≤ m → m ≡ n
leq-anti leq-zero leq-zero             = refl
leq-anti (leq-succ m≤n) (leq-succ n≤m) = cong S (leq-anti m≤n n≤m)
