\begin{code}
{-@ LIQUID "--short-names" @-}

{-# LANGUAGE PartialTypeSignatures #-}

module Lec_1_16 where 

import Prelude hiding (sum)
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

          

tests =  [ assert (sum 0 == 0)              -- VC 1
         , assert (sum 1 == 1) 
         , assert (sum 2 == 3)
         , assert (sum 3 == 6)
         ]


{-@ theorem_stuff :: _ -> { v: _ | sum 2 == 3 } @-}
theorem_stuff :: _ 
theorem_stuff _ = sum 2 
              === 2 + sum 1 
              === 2 + 1 + sum 0
              === 2 + 1 + 0 
              === 3 

{-@ another_theorem :: _ -> { v: _ | sum 3 == 6 } @-}
another_theorem :: _ 
another_theorem _ = sum 3 
                === 3 + sum 2 
                  ? theorem_stuff ()
                === 6

anilTests :: _
anilTests =  
    [ assert (sum 2 == 2 + sum 1)
    , assert (sum 1 == 1 + sum 0)
    , assert (sum 0 == 0)

    ]

-- FORALL n. n <= sum n
{-@ theorem_MJ :: n:Int -> { n <= sum n} @-}
theorem_MJ :: Int -> _ 
theorem_MJ 0 = undefined
 
-- testMJ n = assert (n <= sum n) 

{-@ (=*=) :: x:a -> y:{a | y == x} -> {v:Bool | x == y} @-}
(=*=) :: (Eq a) => a -> a -> Bool 
(=*=) x y = x == y

-- TRUE => (1 + 3 == 4)
\end{code}




