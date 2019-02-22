module Lec_2_13_Termination where

-- | Termination Example 1 --------------------------------------------------------------

{-@ data List [lsize] @-}
data List a = Nil | Cons a (List a)

{-@ measure lsize @-}
{-@ lsize :: List a -> Nat @-} 
lsize :: List a -> Int 
lsize Nil         = 0 
lsize (Cons x xs) = 1 + lsize xs 

lsize1 :: List a -> Int 
lsize1 Nil                  = 0 
lsize1 (Cons _ Nil)         = 1 
lsize1 (Cons x (Cons y zs)) = 2 + lsize1 zs

{- 
  1. LH does not check `silly` as it is not structural recursion
  2. You can define a "metric" by 
      - declaring `lsize1` as a `measure` and
      - typing `silly :: l:List a -> Int / [lsize1 l]
      - associating `lsize` as the "default" size for `List` as `data List [lsize]`
 -}

{-@ silly :: List a -> Int   @-}
silly :: List a -> Int 
silly Nil                  = 0 
silly (Cons _ Nil)         = 1 
silly (Cons x (Cons y zs)) = 1 + silly (Cons x zs)


--------------------------------------------------------


-- | Termination Example 1 --------------------------------------------------------------

data AExp  
  = N Int
  | V String 
  | Plus AExp AExp 

{-@ measure asize @-}
{-@ asize :: AExp -> {v:Int | v >= 1} @-}
asize :: AExp -> Int 
asize (N _) = 1 
asize (V _) = 1 
asize (Plus a1 a2) = 1 + asize a1 + asize a2 

{- 
  merge_exps is not structural recursion 
  1. you can declare `asize` as a `measure`
  2. you can use a "lexicographic" metric `[asize a2, asize a1]`
  3. you can be clever and write a single `[(2 * asize a2) + asize a1)]
 -}

{-@ merge_exps:: a1:AExp -> a2:AExp -> AExp / [(2 * asize a2) + asize a1] @-}
merge_exps:: AExp -> AExp -> AExp
merge_exps (N n1) (N n2)          = N (n1 + n2)
merge_exps (V x1) (V x2)          = Plus (V x1) (Plus (V x2) (N 0))
merge_exps (V x)  (N n)           = Plus (V x) (N n)
merge_exps (N n)  (V x)           = Plus (V x) (N n)
merge_exps (N n) a2               = merge_exps a2 (N n)
merge_exps (V x) a2               = merge_exps a2 (V x)
merge_exps (Plus (V x) a1') a2    = Plus (V x) (merge_exps a1' a2)
merge_exps (Plus _ _) _           = N 0


-- | Termination Example 2 --------------------------------------------------------------

data Pred
  = Var Int             -- ^ x, y, z    variables
  | Not Pred            -- ^ ~ p        negation
  | Or  Pred Pred       -- ^ p1 \/ p2   disjunction
  | And Pred Pred       -- ^ p1 /\ p2   conjunction

{-@ data Pred [psize] @-}

{-@ measure psize @-}
{-@ psize :: Pred -> {v:Int | v >= 0} @-}
psize :: Pred -> Int 
psize (Var _)   = 0
psize (Not p)   = 1 + psize p
psize (Or p q)  = 2 + psize p + psize q
psize (And p q) = 2 + psize p + psize q

{-@ type NNF = {v:Pred | isNNF v} @-}

{-@ measure isNNF @-}
isNNF :: Pred -> Bool
isNNF (Var _)   = True
isNNF (And p q) = isNNF p && isNNF q
isNNF (Or  p q) = isNNF p && isNNF q
isNNF (Not p)   = isVar p

{-@ measure isVar @-}
isVar :: Pred -> Bool
isVar (Var _) = True
isVar _       = False

{- 
  nnf is not structural recursion 
  1. you can declare `psize` as a `measure`
  2. you can specify a metric in the type `nnf :: p:Pred -> Pred / [psize p]` 
  3. you can declare `psize` as a default size `data Pred [psize]`
 -}

{-@ nnf :: Pred -> Pred @-}
nnf :: Pred -> Pred
nnf (Not (And p1 p2)) = Or  (nnf (Not p1)) (nnf (Not p2))
nnf (Not (Or p1 p2))  = And (nnf (Not p1)) (nnf (Not p2))
nnf p                 = p
