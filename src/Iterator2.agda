module Iterator2 where

open import Bool
open import List

module _ (T : Set)(_==_ : T → T → 𝔹) where

  record Iterator : Set where
    constructor _,_,_
    field
      stack₁ : List T
      value  : T
      stack₂ : List T
  
  prev : Iterator → Iterator
  prev a@([] , _ , _) = a
  prev ((x :: xs) , i , l) = (xs , x , (i :: l))
  
  next : Iterator → Iterator
  next a@(_ , _ , []) = a
  next (l , i , (x :: xs)) = ((i :: l) , x , xs)
  
  read : Iterator → T
  read (_ , v , _) = v
  
  backTo : Iterator → T → Iterator
  backTo (s₁ , i , s₂) v = f s₁ i s₂ v
    where
      f : List T → T → List T → T → Iterator
      f [] i s₂ _ = ([] , i , s₂)
      f s₁@(x :: xs) i s₂ v with i == v
      ... | true  = (s₁ , i , s₂)
      ... | false = f xs x (i :: s₂) v

  forthTo : Iterator → T → Iterator
  forthTo (s₁ , i , s₂) v = f s₁ i s₂ v
    where
      f : List T → T → List T → T → Iterator
      f s₁ i [] _ = (s₁ , i , [])
      f s₁ i s₂@(x :: xs) v with i == v
      ... | true  = (s₁ , i , s₂)
      ... | false = f (i :: s₁) x xs v
