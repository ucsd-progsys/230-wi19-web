{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--diff"        @-}

{-# LANGUAGE PartialTypeSignatures #-}

module Lec_1_30 where 

import Prelude hiding (sum)

import ProofCombinators
import qualified State as S 

--------------------------------------------------------------------------------
-- | Arithmetic Expressions 
--------------------------------------------------------------------------------

type Val   = Int
type Vname = String

data AExp  
  = N Val 
  | V Vname 
  | Plus AExp AExp 
  deriving (Show)

type State = S.GState Vname Val

{-
s = [("x", 10), ("y", 20) ]
S.set s "x" 105
s' = [("x", 105), ("y", 20) ]
-} 

{-@ reflect aval @-}
aval :: AExp -> State -> Val
aval (N k)        _ = k
aval (V x)        s = S.get s x
aval (Plus a1 a2) s = (aval a1 s) + (aval a2 s)

--------------------------------------------------------------------------------
-- | Examples
--------------------------------------------------------------------------------

{-@ example :: { v: Int | v == 24 } @-} 
example :: Int
example = aval ex2 state1
  where 
    -- 12 
    ex0 = N 12 
    -- x + 9
    ex1 = (V "x") `Plus` (N 9)
    -- x + y + z
    ex2 = (V "x") `Plus` (V "y") `Plus` (N 4)
    
{-@ reflect state1 @-}
state1 :: State 
state1 = S.init 10 

--------------------------------------------------------------------------------
-- | Constant folding
--------------------------------------------------------------------------------
-- asimp_const 

-- [YES] 4 + 9       ===> 13
-- [YES] x + (4 + 9) ===> x + 13
-- [YES] 2 + (4 + 9) ===> 15 
-- [NO] (x + 4) + 9  ===> x + 13
-- [YES] x + 0       ===> x 

{-@ reflect asimp_const @-}
asimp_const :: AExp -> AExp 
asimp_const (N n) = N n
asimp_const (V x) = V x  
asimp_const (Plus a1 a2) = case (asimp_const a1, asimp_const a2) of 
  (N n1, N n2) -> N (n1 + n2) 
  (b1  , b2)   -> Plus b1 b2

{- type Equiv A1 A2 = s:State -> { aval A1 s == aval A2 s } @-}

{- lem_aval_asimp_const_ok :: a:_ -> Equiv a (asimp_const a) @-} 

{-@ foo :: a:_ -> s:_ -> { aval a s == aval (asimp_const a) s } @-}
foo :: AExp -> State -> Proof 
foo (N n)        _ = ()
foo (V x)        _ = () 
foo (Plus a1 a2) s = case (asimp_const a1, asimp_const a2) of 
    (N n1, N n2) ->  () 
                      ? foo a1 s 
                      ? foo a2 s

    (b1  , b2)   -> () 
                      ? foo a1 s 
                      ? foo a2 s
  



--------------------------------------------------------------------------------
-- | Constant folding with "smart constructor"
--------------------------------------------------------------------------------
-- plus 
-- lemma_aval_plus 
-- HW 

--------------------------------------------------------------------------------
-- | Recursive simplification using "Smart" Constructors
--------------------------------------------------------------------------------
-- asimp 
-- lemma_aval_asimp


--------------------------------------------------------------------------------
-- | Digression: Assignment 
--------------------------------------------------------------------------------

-- substitute "x" with "e" inside "a"
subst :: Vname -> AExp -> AExp -> AExp 
subst x e (Plus a1 a2)   = Plus (subst x e a1) (subst x e a2) 
subst x e (V y) | x == y = e 
subst _ _ a              = a 

{- 

lem_subst :: x:_ -> a:_ -> e:_ -> s:_ 
          -> { aval e (set x (aval a s) s)  == aval (subst x a e) s }


  S     [a > 1000]          the "value" of "replace all occurence of x with a in e"  in s/

    x := a 


  S'    [x > 1000]          the "value" of the "e" in s' 

  WHAT IS 
  
      aval e s' 

  "add" a to e 

 -}

-- DISCUSS

--------------------------------------------------------------------------------
-- | Boolean Expressions and Simplifications 
--------------------------------------------------------------------------------

-- data BExp 
-- bval 
-- simplifications 
-- bNot, bAnd, bLess, bSimp 

--------------------------------------------------------------------------------
-- | Stack Machine 
--------------------------------------------------------------------------------

-- data Instr 
-- type Stack = [Val]

-- exec1, exec 

--------------------------------------------------------------------------------
-- | Compiling Arithmetic Expressions to a Stack Machine 
--------------------------------------------------------------------------------

-- comp 

--------------------------------------------------------------------------------
-- | Correctness of Compilation 
--------------------------------------------------------------------------------

-- thm_comp ... lemma_comp