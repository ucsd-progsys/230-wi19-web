\begin{code}
{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--reflection"  @-}

{-# LANGUAGE PartialTypeSignatures #-}

module Lec_1_18 where 

import Prelude hiding (sum)

import ProofCombinators

-- 1. sum 0 == 0
-- 2. sum n >= 0 

{-@ reflect sum @-}                                 
sum :: Int -> Int 
sum n = if n <= 0 
          then  0                   -- "base"      case 
          else  n + sum (n-1)       -- "recursive" case

{-@ theorem_stuff :: _ -> { v: _ | sum 2 == 3 } @-}
theorem_stuff :: _ 
theorem_stuff _ = sum 2 
              === 2 + sum 1 
              === 2 + 1 + sum 0
              === 2 + 1 + 0 
              === 3 

{-@ another_theorem :: _ -> { v: _ | sum 3 == 6 } @-}
another_theorem :: Int -> _
another_theorem _ = sum 3 
                === 3 + sum 2 
                  ? theorem_stuff ()
                === 6

-- Theorem [MJ] : for all n. n <= sum n



{-@ theorem_MJ :: n:Int -> { n <= sum n} @-}
theorem_MJ :: Int -> Proof 
theorem_MJ _ = undefined

-- for all natural numbers n:  2 * sum n == n * (n + 1)
 -- forall x. Thing(x)
 -- foo :: x -> { Thing x }

{-@ thm_sum :: n:Nat -> { 2 * sum n == n * (n + 1) } @-}
thm_sum :: Int -> Proof 
thm_sum 0 
  =   2 * sum 0 
  === 0 * (0 + 1) 
  *** QED 

thm_sum k 
  =   2 * sum k
  === 2 * (k + (sum (k-1))) 
  === 2 * k + 2 * (sum (k-1))
      ? thm_sum (k-1)
  === k * (k + 1)
  *** QED 

data Peano 
  = Z 
  | S Peano 
  deriving (Eq, Show)

{-@ reflect add @-}
add :: Peano -> Peano -> Peano  
add Z     m = m 
add (S n) m = S (add n m)


{-@ thm_2_add_2_eq_4  :: _ -> { add (S (S Z)) (S (S Z)) == S (S (S (S Z))) }  @-}
thm_2_add_2_eq_4 :: () -> Proof 
thm_2_add_2_eq_4 _ 
  =   add (S (S Z)) (S (S Z)) 
  === S (add (S Z) (S (S Z)))
  === S (S (add Z (S (S Z))))
  === S (S ((S (S Z))))
  === S (S (S (S Z)))
  *** QED 


{-@ thm_add_Z :: p:Peano -> { add Z p == p } @-} 
thm_add_Z :: Peano -> Proof 
thm_add_Z p 
  =   add Z p 
  === p 
  *** QED 

{-@ thm_Z_add :: p:Peano -> { add p Z == p } @-} 
thm_Z_add :: Peano -> Proof 

thm_Z_add Z     
    = add Z Z 
    === Z 
    *** QED 

thm_Z_add (S p) 
    =   add (S p) Z 
    === S (add p Z)
      ? thm_Z_add p
    === S p 
    *** QED 

-- add Z p === p *** QED 
-- >>> add (S (S Z)) (S (S Z)) 
-- S (S (S (S Z)))
\end{code}




