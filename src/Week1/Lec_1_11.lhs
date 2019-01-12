\begin{code}
module Lists where 

import Prelude hiding (lookup, repeat, map, length, head, take, drop)
import qualified Data.Set as S
\end{code}


Goal
====

In order to see some more interesting examples of refinements, 
let's look at a data structure we're all familiar with: lists.

Let's look at some typical functions on lists and see how their 
type can be improved.

Our own list type
=================

Built-in lists and the functions on these already have a lot of 
predefined features in Liquid Haskell. 

To better understand how to define datatypes in Liquid Haskell 
and establish properties on them, let us work with our own lists:

\begin{code}
data List a = Nil | Cons a (List a)
  deriving (Show)

infixr 5 `Cons`
\end{code}

\begin{code}
{-@ length :: List a -> Nat @-}
length :: List a -> Int
length Nil           = 0
length (x `Cons` xs) = 1 + length xs

{-@ measure length @-}

{-@ data List [length] @-} 
\end{code}

\begin{code}
{-@ interleave :: xs:List a -> ys:List a -> List a / [length xs + length ys] @-}
interleave :: List a -> List a -> List a
interleave Nil           ys  = ys
interleave xs            Nil = xs
interleave (x `Cons` xs) ys  = x `Cons` interleave ys xs

{-@ lazy foo @-}
{-@ foo :: Int -> {v:Int | false } @-}
foo :: Int -> Int 
foo n = foo n 

\end{code}


\begin{code}

{-@ head :: {v:_ | length v > 0 } -> _ @-}
head :: List a -> a
head (Cons x _) = x
head _          = impossible "will never happen"

{-@ tail :: {v:_ | length v > 0 } -> _ @-}
tail :: List a -> List a
tail (Cons x xs) = xs
tail Nil         = impossible "tail: Nil"


{-@ test1 :: {v:Int | v == 2 } @-}
test1       = length (take 2 fruits)  
  where 
    fruits = (Cons "apple" (Cons "banana" (Cons "carrot" Nil)) )

{-@ test2 :: {v:Int | v == 1 } @-}
test2       = length (take 20 fruits)  
  where 
    fruits = (Cons "apple" Nil)



-- >>> take 2 
-- >>> Cons "apple" (Cons "ban" Nil)

-- 1. {-@ take :: n:Nat -> _ -> {v:_ | length v == n } @-}

{-@ take :: n:Nat  -> xs:_ -> {v:_ | length v == min n (length xs) } @-}
take :: Int -> List a -> List a
take _ Nil         = Nil
take 0 _           = Nil
take i (Cons x xs) = x `Cons` take (i - 1) xs

{-@ inline min @-}
min :: Int -> Int -> Int 
min x y = if x < y then x else y

-- A. green line & happiness "sparking joy"
-- B. terror inside "take"
-- C. terror inside "test"
-- D. terror inside "take" AND "test"


\end{code}

\begin{code}
{-@ impossible :: { s : String | False } -> a @-}
impossible :: String -> a
impossible msg = error msg
\end{code}

\begin{code}
{-@ setTest :: { x : _ | x == True } @-}
setTest :: Bool 
setTest = ((set1 `S.union` set2) `S.difference` set3) == setR
  where
    set1 = S.fromList [1,2,3]
    set2 = S.fromList [2,4,6]
    set3 = S.fromList [3,4,5]
    setR = S.fromList [1,2,6]
\end{code}


\begin{code}
data Table key val 
  = Empty
  | Bind key val (Table key val)

test55 = lookup "cat" table0 
  where
   table0 :: Table String Int
   table0 = Bind "cat" 10 (Bind "dog" 20 (Bind "mouse" 100 Empty))

{-@ lazy lookup @-}
{-@ lookup :: k:_ -> t:{_ | S.member k (tableKeys t)} -> _ @-}
lookup :: Eq key => key -> Table key val -> val
lookup k (Bind k' v rest)
  | k == k'    = v
  | otherwise  = lookup k rest
lookup _ Empty = impossible "lookup: Empty"

{-@ measure tableKeys @-}
tableKeys :: (Ord k) => Table k v -> S.Set k 
tableKeys Empty           = S.empty 
tableKeys (Bind k _ rest) = (S.singleton k) `S.union` tableKeys rest 

\end{code}

