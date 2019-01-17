






\begin{code}
{-@ LIQUID "--short-names" @-}

module Lec_1_14 where 

import Prelude hiding (sum, assert)
import ProofCombinators


{-@ assert :: {p:Bool | p } -> a -> a @-}
assert :: Bool -> a -> a 
assert True  x = x 
assert False _ = impossible "Yikes assert failed!" 

test0 = assert (1 < 10) 

{-@ lazy mj @-}
mj :: Int -> Int -> Int 
mj x 0 = 1 
mj x n = x * mj x (n-1) 

{-@ plus :: x:_ -> y:_ -> {v:Int | v = x + y } @-} 
plus :: Int -> Int -> Int 
plus x y = x + y

test1 x = assert (x < plus x 1) 

\end{code}

\begin{code}

-- 1. sum 0 == 0
-- 2. sum n >= 0 

{-@ reflect sum @-}                                 
sum :: Int -> Int 
sum n = if n <= 0 
          then  0                   -- "base"      case 
          else  n + sum (n-1)       -- "recursive" case

          
-- testMJ n = assert (n <= sum n) 

tests =  [ assert (sum 0 == 0)              -- VC 1
         , assert (sum 1 == 1) 
         -- , assert (sum 2 == 3)
         , assert (sum 3 == 6)
         ]

\end{code}




