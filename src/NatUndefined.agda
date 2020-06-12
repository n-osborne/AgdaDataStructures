module NatUndefined where

data Nat : Set where
  undef : Nat
  zero : Nat
  succ : Nat -> Nat

_+_ : Nat -> Nat -> Nat
m + undef = undef
m + zero = m
undef + succ n = undef
zero + succ n = succ (zero + n)
succ m + succ n = succ (succ m + n)

_-_ : Nat -> Nat -> Nat
m - undef = undef
m - zero = m
undef - succ n = undef
zero - succ n = undef
succ m - succ n = m - n

-- TODO: prove some properties
