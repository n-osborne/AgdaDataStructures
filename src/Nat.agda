{-# OPTIONS --allow-unsolved-metas #-}

module Nat where

open import Agda.Primitive
open import Bool renaming (¬ to not)
open import IdentityRelation


data ℕ : Set where
  O : ℕ
  S : ℕ -> ℕ

-- picked from HoFF-UF
ℕ-ind : (A : ℕ → Set)               -- Property
        → A O                       -- case O
        → ((n : ℕ) → A n → A (S n)) -- induction case: f
        → (n : ℕ) → A n             -- h
ℕ-ind A a₀ f = h
  where
    h : (n : ℕ) → A n
    h O  = a₀
    h (S n) = f n (h n)

ℕ-rec : {A : Set}
        → A
        → (ℕ → A → A)
        → ℕ → A
ℕ-rec {A} a₀ f n = ℕ-ind (λ _ → A) a₀ f n

ℕ-ite : {A : Set}
        → A
        → (A → A)
        → ℕ → A
ℕ-ite a₀ f n = ℕ-rec a₀ (λ _ → f) n


data _≤_ : ℕ -> ℕ -> Set where
  `Z : ∀ {n} -> O ≤ n
  `S : ∀ {n m} -> n ≤ m -> S n ≤ S m

diff : ∀ {n m} -> n ≤ m -> ℕ
diff {.O} {m} `Z = m
diff {.(S _)} {.(S _)} (`S p) = S (diff p)

data ⊥ : Set where

¬ : Set -> Set
¬ P = P -> ⊥

_≰_ : ℕ -> ℕ -> Set
n ≰ m = ¬ (n ≤ m) 

data Dec (P : Set) : Set where
  yes : P -> Dec P
  no  : (P -> ⊥) -> Dec P

¬s≤z : ∀ {n : ℕ} -> ¬ (S n ≤ O)
¬s≤z = λ ()

¬s≤s : ∀ {n m} -> ¬ (n ≤ m) -> ¬ (S n ≤ S m)
¬s≤s ¬n≤m (`S n≤m) = ¬n≤m n≤m

_≤?_ : (n : ℕ) -> (m : ℕ) -> Dec (n ≤ m)
O ≤? m = yes `Z
S n ≤? O = no (λ ())
S n ≤? S m with n ≤? m
... | yes n≤m = yes (`S n≤m)
... | no ¬n≤m = no (¬s≤s ¬n≤m)

_≡ᵇ_ : ℕ → ℕ → 𝔹
O     ≡ᵇ O     = true
(S n) ≡ᵇ (S m) = n ≡ᵇ m
(S _) ≡ᵇ O     = false
O     ≡ᵇ (S _) = false

_<ᵇ_ : ℕ → ℕ → 𝔹
O     <ᵇ (S n) = true
(S n) <ᵇ (S m) = n <ᵇ m
_     <ᵇ _     = false

_≤ᵇ_ : ℕ → ℕ → 𝔹
m ≤ᵇ n = (m <ᵇ n) ∨ (m ≡ᵇ n)

_>ᵇ_ : ℕ → ℕ → 𝔹
m >ᵇ n = not (m ≤ᵇ n)

_≥ᵇ_ : ℕ → ℕ → 𝔹
m ≥ᵇ n = not (m <ᵇ n)

max : ℕ → ℕ → ℕ
max O m = m
max (S n) O = S n
max (S n) (S m) = max n m


module Classical-Definitions where
  -- classical definition of addition with explicit recursion on second argument
  _+_ : ℕ -> ℕ -> ℕ
  n + O     = n
  n + (S m) = S (n + m)

  _-_ : ℕ → ℕ → ℕ
  n     - O     = n
  O     - (S _) = O
  (S n) - (S m) = n - m
  
  _*_ : ℕ → ℕ → ℕ
  _ * O     = O
  n * (S m) = n + (n * m)

  _+[_]_ : ℕ -> ℕ -> ℕ → ℕ
  a +[ n ] O = {!!}
  a +[ n ] S b = {!!}



module HoFF-UF-inspired-Definitions where

  infix 20 _+_
  -- note: in HoFF-UF, addition is defined by iteration
  -- in classical definition of n + m we apply `n` times `S` on `m`
  _+_ : ℕ → ℕ → ℕ
  n + m = ℕ-ite n S m

  +-comm : {m n : ℕ} → n + m ≡ m + n
  +-comm {n = O}   = {!!}
  +-comm {n = S n} = {!!}
  
  +-O-right-neutral : {n : ℕ} → n ≡ n + O
  +-O-right-neutral = {!!}
  
  +-commutative : {m n : ℕ} → (n + m) ≡ (m + n)
  +-commutative {m} = ℕ-ind (λ n → (n + m) ≡ (m + n)) {!!} {!!} {!!}

