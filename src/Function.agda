module Function where

_∘_ : {A B C : Set} → (B → C) → (A → B) → A → C
g ∘ f = λ a → g (f a)

id : {A : Set} → A → A
id a = a
