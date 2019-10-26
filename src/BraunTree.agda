module BraunTree where

-- in this module we use the standard library because we need a bunch of properties
open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Sum
open import Data.List

data Tree (A : Set) : Set where
  empty : Tree A
  node  : A → Tree A → Tree A → Tree A

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
n₁ eq-or-suc? n₂ | no n₁≢n₂ | no  n₁≢sn₂  = too-far n₁ n₂ n₁≢n₂ n₁≢sn₂


-- View for BraunTree
data IsItBraunTree {A : Set} : Tree A → Set where
  emptyBraun : IsItBraunTree empty
  nodeBraun  : (a : A)(l r : Tree A) → (size l) ≡ (size r) ⊎ (size l) ≡ suc (size r) → IsItBraunTree (node a l r)
  not-Braun  : (a : A)(l r : Tree A) → ¬ (size l ≡ size r) → ¬ (size l ≡ (suc (size r))) → IsItBraunTree (node a l r)


isBraunTree? : {A : Set}(t : Tree A) → IsItBraunTree t
isBraunTree? empty = emptyBraun
isBraunTree? (node x l r) with (size l) eq-or-suc? (size r) 
isBraunTree? (node x l r) | eq n₁ n₂ n₁≡n₂              = nodeBraun x l r (inj₁ n₁≡n₂)
isBraunTree? (node x l r) | is-suc n₁ n₂ n₁≡sn₂         = nodeBraun x l r (inj₂ n₁≡sn₂) 
isBraunTree? (node x l r) | too-far n₁ n₂ n₁≢n₂ n₁≢sn₂  = not-Braun x l r n₁≢n₂ n₁≢sn₂

-- The simple version of insert
insert : {A : Set} → A → Tree A → Tree A
insert a empty = node a empty empty
insert a (node x l r) = node x (insert a r) l

-- A version of insertion with checks inside (return an empty tree if can not balance)
-- Not really a good idea, this is just to use views
insert-check : {A : Set} →  A → Tree A → Tree A
insert-check a empty = node a empty empty
insert-check a (node x l r) with isBraunTree? (node x l r)
insert-check a (node x l r) | nodeBraun x l r (inj₁ n₁≡n₂)  = node x (insert-check a l) r
insert-check a (node x l r) | nodeBraun x l r (inj₂ n₁≡sn₂) = node x (insert-check a r) l
insert-check a (node x l r) | not-Braun _ _ _ _ _           = empty

data IsBalanced {A : Set} : Tree A → Set where
  empty-bal : IsBalanced empty
  node-bal  :  (a : A)(l r : Tree A) → (size l) ≡ (size r) ⊎ (size l) ≡ suc (size r) → IsBalanced (node a l r)

lemma-insert-inc-size : ∀ {A : Set}(a : A)(t : Tree A) → size (insert a t) ≡ suc (size t)
lemma-insert-inc-size a empty = refl
lemma-insert-inc-size a (node x l r) rewrite +-suc (size r) (size l) = cong suc {!!}    --  (lemma-insert-inc-size a r)

lemma-insert-braun-tree : ∀ {A : Set}(a : A)(t : Tree A) → IsBalanced t → IsBalanced (insert a t)
lemma-insert-braun-tree a empty empyt-bal = node-bal a empty empty (inj₁ refl)
lemma-insert-braun-tree a (node x l r) (node-bal x l r (inj₁ sl≡sr))  = node-bal x (insert a r) l (inj₂ {!!})
lemma-insert-braun-tree a (node x l r) (node-bal x l r (inj₂ sl≡ssr)) = node-bal x (insert a r) l (inj₁ {!!})


-- same idea than insert-check, but take only balanced trees as a proof must be given
insert-check₂ : {A : Set}(a : A)(t : Tree A)(prf : IsBalanced t) → Tree A
insert-check₂ a empty prf = empty
insert-check₂ a (node x l r) (node-bal x l r (inj₁ sl≡sr))  = {!!} 
insert-check₂ a (node x l r) (node-bal x l r (inj₂ sl≡ssr)) = {!!}

