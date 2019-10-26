module BraunTree where

-- in this module we use the standard library because we need a bunch of properties
open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Sum
open import Data.List

-- Binary tree data structure
data Tree (A : Set) : Set where
  empty : Tree A
  node  : A → Tree A → Tree A → Tree A

-- some primitives
to-list : {A : Set} → Tree A → List A
to-list empty = []
to-list (node x l r) = x ∷ (to-list l) ++ (to-list r)

size : {A : Set} → Tree A → ℕ
size empty = zero
size (node x l r) = suc (size r) + size l

-- View for equal or immediate successor
data Eq-or-suc : ℕ → ℕ → Set where
  eq      : (n₁ n₂ : ℕ) → n₁ ≡ n₂       → Eq-or-suc n₁ n₂
  is-suc  : (n₁ n₂ : ℕ) → n₁ ≡ (suc n₂) → Eq-or-suc n₁ n₂
  too-far  : (n₁ n₂ : ℕ) → ¬ (n₁ ≡ n₂)   → ¬ (n₁ ≡ (suc n₂)) → Eq-or-suc n₁ n₂

_eq-or-suc?_ : (n₁ : ℕ) → (n₂ : ℕ) → Eq-or-suc n₁ n₂
n₁ eq-or-suc? n₂ with  n₁ ≟ n₂
n₁ eq-or-suc? n₂ | yes n₁≡n₂ = eq n₁ n₂ n₁≡n₂
n₁ eq-or-suc? n₂ | no _ with n₁ ≟ (suc n₂)
n₁ eq-or-suc? n₂ | _         | yes n₁≡sn₂  = is-suc n₁ n₂ n₁≡sn₂
n₁ eq-or-suc? n₂ | no n₁≢n₂  | no  n₁≢sn₂  = too-far n₁ n₂ n₁≢n₂ n₁≢sn₂


-- Views for balanced Trees
data IsBalanced {A : Set} : Tree A → Set where
  empty-bal     : IsBalanced empty
  same-size-bal : (a : A)(l r : Tree A) → (size l) ≡ (size r) → IsBalanced (node a l r)
  suc-size-bal  : (a : A)(l r : Tree A) → (size l) ≡ suc (size r) → IsBalanced (node a l r)
  not-balanced  : (a : A)(l r : Tree A) → ¬ (size l ≡ size r) → ¬ (size l ≡ (suc (size r))) → IsBalanced (node a l r)

isBalanced? : {A : Set}(t : Tree A) → IsBalanced t
isBalanced? empty = empty-bal
isBalanced? (node x l r) with (size l) eq-or-suc? (size r) 
isBalanced? (node x l r) | eq n₁ n₂ n₁≡n₂              = same-size-bal x l r n₁≡n₂
isBalanced? (node x l r) | is-suc n₁ n₂ n₁≡sn₂         = suc-size-bal x l r n₁≡sn₂
isBalanced? (node x l r) | too-far n₁ n₂ n₁≢n₂ n₁≢sn₂  = not-balanced x l r n₁≢n₂ n₁≢sn₂

destruct-IsBalanced : {A : Set}{t : Tree A} → IsBalanced t → Tree A
destruct-IsBalanced empty-bal = empty
destruct-IsBalanced (same-size-bal a l r _) = node a l r
destruct-IsBalanced (suc-size-bal a l r _) = node a l r
destruct-IsBalanced (not-balanced a l r _ _) = node a l r


-- The simple version of insert
insert : {A : Set} → A → Tree A → Tree A
insert a empty = node a empty empty
insert a (node x l r) = node x (insert a r) l

-- A version of insertion with checks inside (return an empty tree if can not balance)
-- Not really a good idea, this is just to use views
insert-check : {A : Set} →  A → Tree A → Tree A
insert-check a empty = node a empty empty
insert-check a (node x l r) with isBalanced? (node x l r)
insert-check a (node x l r) | same-size-bal x l r n₁≡n₂ = node x (insert-check a l) r
insert-check a (node x l r) | suc-size-bal x l r n₁≡sn₂ = node x (insert-check a r) l
insert-check a (node x l r) | not-balanced _ _ _ _ _    = empty

-- A record type to contain a Tree and its balancinf together
record BalancedTree (A : Set) : Set where
  constructor BTree
  field
    tree  : Tree A
    proof : IsBalanced tree

balancedTree : {A : Set} → Tree A → BalancedTree A
balancedTree empty = BTree empty empty-bal
balancedTree (node x l r) with (size l) eq-or-suc? (size r)
balancedTree (node x l r) | eq sl sr sl≡sr             = BTree (node x l r) (same-size-bal x l r sl≡sr)
balancedTree (node x l r) | is-suc sl sr sl≡ssr        = BTree (node x l r) (suc-size-bal x l r sl≡ssr)
balancedTree (node x l r) | too-far sl sr sl≢sr sl≢ssr = BTree (node x l r) (not-balanced x l r sl≢sr sl≢ssr)

insert-balanced : {A : Set}(a : A)(t : Tree A) → BalancedTree A
insert-balanced a empty = BTree (node a empty empty) (same-size-bal a empty empty refl)
insert-balanced a (node x l r) with insert-balanced a r
insert-balanced a (node x l r) | BTree empty empty-bal = BTree (node x (node a empty empty) empty) (suc-size-bal x (node a empty empty) empty refl)
insert-balanced a (node x l r) | BTree (node xr lr rr) (same-size-bal xr lr rr slr≡srr) = BTree (node x (node xr lr rr) l) {!!}
insert-balanced a (node x l r) | BTree (node xr lr rr) (suc-size-bal xr lr rr slr≡ssrr) = BTree (node x (node xr lr rr) l) {!!}
insert-balanced a (node x l r) | BTree (node xr lr rr) (not-balanced xr lr rr p1 p2)    = BTree (node x (node xr lr rr) l) {!!}

{--

lemma-insert-inc-size : ∀ {A : Set}(a : A)(t : Tree A) → size (insert a t) ≡ suc (size t)
lemma-insert-inc-size a empty = refl
lemma-insert-inc-size a (node x l r) rewrite +-suc (size r) (size l) = cong suc {!!}    --  (lemma-insert-inc-size a r)


-}


