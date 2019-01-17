\begin{code}
module Sets where 

import           Prelude hiding (lookup)
import qualified Data.Set as S

{-@ impossible :: { s : String | False } -> a @-}
impossible :: String -> a
impossible msg = error msg
\end{code}

Liquid Haskell comes with a number of useful specifications for standard libraries. 
One such example is that it comes with specifications for `Data.Set`

\begin{code}
import qualified Data.Set as S
\end{code}


Uninterpreted functions
=======================

Liquid Haskell allows us to give refined interfaces to trusted libraries without verifying them completely.

Here is an example:

\begin{code}
{-@ measure checked :: [Int] -> Bool @-}

{-@ assume check :: xs : [Int] -> { b : Bool | b <=> checked xs } @-}
check :: [Int] -> Bool
check xs = sum xs == 0
\end{code}

The function checked is an **uninterpreted function**. 

Such a function can be introduced using a measure directive 
with just a type signature, and  **no actual definition** 
in the code.

We can still teach Liquid Haskell facts about the behaviour 
of such a function.

The assume directive assumes a type without verifying it. 

Here, we say if and only if check succeeds, it establishes 
  the checked predicate for the checked list.


Using an uninterpreted function
===============================

We can go on to work with checked lists.

\begin{code}
{-@ type CheckedList = { xs : [Int] | checked xs } @-}

{-@ assume combine :: CheckedList -> CheckedList -> CheckedList @-}
combine :: [Int] -> [Int] -> [Int]
combine xs ys = xs ++ ys
\end{code}

And this is rejected:

\begin{code}
test :: IO ()
test = do
  xs <- readLn
  ys <- readLn
  print $ combine xs ys
\end{code}

Can you fix it?

Sets
===

The specification for sets introduces a number of uninterpreted functions, 
equips the functions from the `Data.Set` library with refined types mentioning 
these functions, and then maps these functions to SMT solver primitives being 
able to reason about sets (ok, that makes them no longer entirely uninterpreted):

That is, the library specifications say that:

   S.union  :: s1:Set a -> s2:Set a -> {v:Set a | v = union s1 s2}
   S.member :: x:Set a  -> s:Set a  -> {b:Bool | b <=> member x s}

That is, the specification for sets introduces a number of 
uninterpreted functions, equips the functions from the `Data.Set` 
library with refined types mentioning these functions, and then 
maps these functions to SMT solver primitives being able to 
reason about sets 

\begin{code}
{-@ setTest :: { x : S.Set Int | S.member 2 x && not (S.member 4 x) } @-}
setTest :: S.Set Int
setTest = (set1 `S.union` set2) `S.difference` set3
  where
    set1 = S.fromList [1,2,3]
    set2 = S.fromList [2,4,6]
    set3 = S.fromList [3,4,5]
\end{code}

We can use sets in refinements ...

Lookup tables
=============

Let's consider a primitive lookup table:

\begin{code}
data Table key val 
  = Empty
  | Bind key val (Table key val)
\end{code}

As for lists, we start by defining a termination measure:

\begin{code}
{-@ measure size @-}
{-@ size :: Table key val -> Nat @-}
size :: Table key val -> Int
size Empty        = 0
size (Bind _ _ t) = 1 + size t

{-@ data Table [size] @-}
\end{code}

Another measure on maps
=======================

\begin{code}
{-@ measure keys @-}
keys :: Ord key => Table key val -> S.Set key
keys Empty        = S.empty
keys (Bind k _ t) = S.union (S.singleton k) (keys t)
\end{code}

If we have multiple measures on a datatype (here Table), 
then the constructor types are refined by all of them, e.g.:

    Empty :: {t : Table key val |  size t == 0 
                                && keys t == S.empty }

    Bind  :: k:key -> v:val -> t0:Table key val 
          -> {t : Table key val | size t' = 1 + size t0 
                                && keys t' = S.union (S.singleton k) (keys t0) }

A safe lookup function
======================

\begin{code}
lookup :: Ord key => key -> Table key val -> val
lookup k (Bind k' v r)
  | k == k'            = v
  | otherwise          = lookup k r
lookup _ Empty         = impossible "lookup: Empty"
\end{code}

Can you provide a type signature for lookup that makes it check?

Let's test:

lookupTest1 :: Int
lookupTest1 = lookup "y" (Bind "x" 23 (Bind "y" 45 (Bind "z" 56 Empty))) -- ok

lookupTest2 :: Int
lookupTest2 = lookup "p" (Bind "x" 23 (Bind "y" 45 (Bind "z" 56 Empty))) -- should fail
\end{code}

Removing bindings
=================

Can you provide a refined type signature for delete? 

\begin{code}
delete :: Ord key => key -> Table key val -> Table key val
delete _ Empty         = Empty
delete k (Bind k' v r)
  | k == k'            = delete k r
  | otherwise          = Bind k' v (delete k r)
\end{code}

Could / should we replace anything with impossible here?