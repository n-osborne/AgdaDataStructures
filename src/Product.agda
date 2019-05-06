module Product where

data Prod (A B : Set) : Set where
  _×_ : A → B → Prod A B

fst : {A B : Set} → Prod A B → A
fst (a × _) = a

snd : {A B : Set} → Prod A B → B
snd (_ × b) = b


  
