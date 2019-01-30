{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}

{-# LANGUAGE PartialTypeSignatures #-}

module Lec_1_30 where 

import Prelude hiding (sum)

import ProofCombinators
import qualified State as S 

type Val   = Int
type Vname = String

data AExp  
  = N Val 
  | V Vname 
  | Plus AExp AExp 
  deriving (Show)

type State = S.GState Vname Val

{-@ reflect aval @-}
aval :: AExp -> State -> Val
aval (N k)        _ = k
aval (V x)        s = S.get s x
aval (Plus a1 a2) s = (aval a1 s) + (aval a2 s)

-- Examples

{-@ foog :: { v: Int | v == 30 } @-} 
foog :: Int
foog = aval ex2 state1
  where 
    -- 12 
    ex0 = N 12 
    -- x + 9
    ex1 = Plus (V "x") (N 9)
    -- x + y + z
    ex2 = Plus (V "x") (Plus (V "y") (V "z"))
    
{-@ reflect state1 @-}
state1 :: State 
state1 = S.init 10 

-- Constant folding

-- asimp_const 
-- lemma_aval_asimp_const 


-- Constant folding with "smart constructor"
-- plus 
-- lemma_aval_plus 
-- asimp 
-- lemma_aval_asimp

-------

--- [ASIDE] Boolean Expressions 
-- data BExp 
-- bval 

-- simplifications 

-- bNot, bAnd, bLess, bSimp 


-------

-- Stack Machine 

-- data Instr 
-- type Stack = [Val]

-- exec1, exec 
-- comp 
-- thm_comp ... lemma_comp