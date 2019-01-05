{-@ LIQUID "--no-termination" @-}
module Lec02 where

import Text.Printf (printf)
import Debug.Trace (trace)

incr :: Int -> Int
incr x = x + 1

zincr :: Int -> Int
zincr = \x -> x + 1

eleven = incr (10 + 2)
-- sumList xs = case xs of
               -- []     -> 0
               -- (x:xs) -> x + sumList xs

sumList :: [Int] -> Int
sumList []     = 0
sumList (x:xs) = x + sumList xs

isOdd x = x `mod` 2 == 1

oddsBelow100 = myfilter isOdd [0..100]

myfilter f []      = []
myfilter f (x:xs') = if f x then x : rest else rest
  where
    rest           = myfilter f xs'

neg :: (a -> Bool) -> (a -> Bool)
neg f = \x -> not (f x)

isEven = neg isOdd

partition p xs = (myfilter p xs, myfilter (neg p) xs)



sort []     = []
sort (x:xs) = sort ls ++ [x] ++ sort rs
   where
      ls    = [ y | y <- xs, y < x  ]
      rs    = [ z | z <- xs, x <= z ]


quiz   = [x * 10 | x <- xs, x > 3]
  where
    xs = [0..5]






























data Expr
  = Number Double
  | Plus   Expr Expr
  | Minus  Expr Expr
  | Times  Expr Expr
  deriving (Eq, Ord, Show)

eval :: Expr -> Double
eval e = case e of
  Number n    -> n
  Plus  e1 e2 -> eval e1 + eval e2
  Minus e1 e2 -> eval e1 - eval e2
  Times e1 e2 -> eval e1 * eval e2

ex0 :: Expr
ex0 = Number 5

ex1 :: Expr
ex1 = Plus ex0 (Number 7)

ex2 :: Expr
ex2 = Minus (Number 4) (Number 2)

ex3 :: Expr
ex3 = Times ex1 ex2



fact :: Int -> Int
fact n  = trace msg res
  where
    msg = printf "Fact n = %d res = %d\n" n res 
    res = if n <= 0 then 0 else n * fact (n-1)

{-
-- fact :: Int -> Int
let rec fact n =
  let res = if n <= 0 then 0 else n * fact (n-1) in
  let _   = Printf.printf "Fact n = %d res = %d\n" n res in
  res
-}














----
