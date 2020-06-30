module Group where

open import IdentityRelation

record Group (S : Set) : Set₁ where
  field
    op              : S -> S -> S
    op-assoc        : ∀ x y z -> op x (op y z) ≡ op (op x y) z
    ε               : S
    ε-neutral-left  : ∀ x -> op ε x ≡ x
    ε-neutral-right : ∀ x -> op x ε ≡ x
    inv             : S -> S
    sym             : ∀ x -> op x (inv x) ≡ ε
open Group public

record AbelianGroup (S : Set) : Set₁ where
  field
    G       : Group S
    op-comm : ∀ (x y : S) -> op G x y ≡ op G y x
open AbelianGroup public
