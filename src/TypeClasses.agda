module TypeClasses where

open import Bool

record Eq {a} (A : Set a) : Set a where
  field
    _==_ : A → A → 𝔹


