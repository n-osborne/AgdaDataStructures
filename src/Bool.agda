module Bool where

data 𝔹 : Set where
  true  : 𝔹
  false : 𝔹

_∧_ : 𝔹 → 𝔹 → 𝔹
false ∧ _ = false
true  ∧ b = b

_∨_ : 𝔹 → 𝔹 → 𝔹
true  ∨ _ = true
false ∨ b = b

¬ : 𝔹 → 𝔹
¬ true  = false
¬ false = true
