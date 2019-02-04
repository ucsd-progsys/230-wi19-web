{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{-@ LIQUID "--diff"       @-}
{-@ infixr ++             @-}  -- TODO: Silly to have to rewrite this annotation!

{-# LANGUAGE PartialTypeSignatures #-}

module Expressions where

import           Prelude hiding ((++), const, sum) 
import           ProofCombinators
import           Lists
import qualified State as S 

--------------------------------------------------------------------------------
-- | Arithmetic Expressions 
--------------------------------------------------------------------------------
type Vname = String

data AExp  
  = N Val 
  | V Vname 
  | Plus AExp AExp 
  deriving (Show)

type Val   = Int 
type State = S.GState Vname Val 

{-@ reflect aval @-}
aval                :: AExp -> State -> Val 
aval (N n) _        = n 
aval (V x) s        = S.get s x 
aval (Plus e1 e2) s = aval e1 s + aval e2 s

--------------------------------------------------------------------------------
-- | Example Expressions 
--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------
-- | Constant Folding 
--------------------------------------------------------------------------------

{-@ reflect asimp_const @-}
asimp_const :: AExp -> AExp 
asimp_const (N n) = N n
asimp_const (V x) = V x  
asimp_const (Plus a1 a2) = case (asimp_const a1, asimp_const a2) of 
  (N n1, N n2) -> N (n1 + n2) 
  (b1  , b2)   -> Plus b1 b2

{-@ lemma_aval_asimp_const :: a:_ -> s:_ -> { aval (asimp_const a) s = aval a s } @-}
lemma_aval_asimp_const :: AExp -> State -> Proof
lemma_aval_asimp_const (N _) _ 
  = ()
lemma_aval_asimp_const (V _) _ 
  = ()
lemma_aval_asimp_const (Plus a1 a2) s 
  = case (asimp_const a1, asimp_const a2) of 
      (N _, N _) -> lemma_aval_asimp_const a1 s &&& lemma_aval_asimp_const a2 s 
      (_  , _)   -> lemma_aval_asimp_const a1 s &&& lemma_aval_asimp_const a2 s 

--------------------------------------------------------------------------------
-- | Q: Why is the "case-of" important in the proof?
--------------------------------------------------------------------------------

{-@ reflect silly @-}
silly :: AExp -> Int 
silly (N _)        = 0
silly (V _)        = 0 
silly (Plus a1 a2) = silly a1 + silly a2 

{-@ lem_silly :: a:_ -> { silly a == 0 } @-} 
lem_silly :: AExp -> Proof 
lem_silly (N _)      = () 
lem_silly (V _)      = () 
lem_silly (Plus a1 a2) = lem_silly a1 &&& lem_silly a2  

--------------------------------------------------------------------------------
-- | "Smart" Constructors
--------------------------------------------------------------------------------

{-@ reflect plus @-}
plus :: AExp -> AExp -> AExp 
plus (N i1) (N i2) = N (i1+i2) 
plus (N 0)  a      = a 
plus a      (N 0)  = a 
plus a1     a2     = Plus a1 a2

{-@ lemma_aval_plus :: a1:_ -> a2:_ -> s:_ -> 
      { aval (plus a1 a2) s = aval (Plus a1 a2) s } 
  @-}
lemma_aval_plus :: AExp -> AExp -> State -> Proof 
lemma_aval_plus (N _) (N _) _ = () 
lemma_aval_plus (N 0) a     _ = () 
lemma_aval_plus a     (N 0) _ = () 
lemma_aval_plus a1    a2    _ = () 

--------------------------------------------------------------------------------
-- | Recursive simplification using "Smart" Constructors
--------------------------------------------------------------------------------
{-@ reflect asimp @-}
asimp :: AExp -> AExp 
asimp (Plus a1 a2) = plus (asimp a1) (asimp a2)
asimp a            = a 

{-@ lemma_aval_asimp :: a:_ -> s:_ -> { aval (asimp a) s = aval a s } @-}
lemma_aval_asimp :: AExp -> State -> Proof 
lemma_aval_asimp (Plus a1 a2) s 
   =   lemma_aval_asimp a1 s 
   &&& lemma_aval_asimp a2 s 
   &&& lemma_aval_plus (asimp a1) (asimp a2) s
lemma_aval_asimp _ _ 
   =  () 

--------------------------------------------------------------------------------
-- | Digression: Assignment 
--------------------------------------------------------------------------------
{- 

    s 

        x := a 

    s' 

    How will you relate value of some expression `e` in `s'` and `s`? 

  -}

{-@ reflect subst @-}
subst :: Vname -> AExp -> AExp -> AExp 
subst x e (Plus a1 a2)   = Plus (subst x e a1) (subst x e a2) 
subst x e (V y) | x == y = e 
subst _ _ a              = a 

--------------------------------------------------------------------------------
-- | Boolean Expressions 
--------------------------------------------------------------------------------

data BExp 
  = Bc   Bool 
  | Not  BExp 
  | And  BExp BExp 
  | Less AExp AExp 
  deriving (Show)

{-@ reflect bOr @-}
bOr :: BExp -> BExp -> BExp 
bOr b1 b2 = Not ((Not b1) `And` (Not b2))
       
{-@ reflect bImp @-}
bImp :: BExp -> BExp -> BExp 
bImp b1 b2 = bOr (Not b1) b2

{-@ reflect bval @-}
bval :: BExp -> State -> Bool
bval (Bc   b)     s = b 
bval (Not  b)     s = not (bval b s) 
bval (And  b1 b2) s = bval b1 s && bval b2 s 
bval (Less a1 a2) s = aval a1 s <  aval a2 s 

{-@ reflect bNot @-}
bNot :: BExp -> BExp 
bNot (Bc True)  = Bc False 
bNot (Bc False) = Bc True 
bNot b          = Not b

{-@ reflect bAnd @-}
bAnd :: BExp -> BExp -> BExp 
bAnd (Bc True)  b          = b
bAnd b          (Bc True)  = b
bAnd (Bc False) b          = Bc False
bAnd b          (Bc False) = Bc False
bAnd b1         b2         = And b1 b2

{-@ reflect bLess @-}
bLess :: AExp -> AExp -> BExp 
bLess (N n1) (N n2) = Bc (n1 < n2) 
bLess a1     a2     = Less a1 a2

{-@ reflect bsimp @-}
bsimp :: BExp -> BExp
bsimp (Bc v)       = Bc v 
bsimp (Not b)      = bNot  (bsimp b)
bsimp (And b1 b2)  = bAnd  (bsimp b1) (bsimp b2)
bsimp (Less a1 a2) = bLess (asimp a1) (asimp a2)

--------------------------------------------------------------------------------
-- | Stack Machine 
--------------------------------------------------------------------------------
data Instr 
  = LOADI Val 
  | LOAD  Vname 
  | ADD
  deriving (Show)

type Stack = [Val]

{-@ reflect exec1 @-}
exec1 :: Instr -> State -> Stack -> Stack
exec1 (LOADI n) _ stk       = n           : stk 
exec1 (LOAD x)  s stk       = (S.get s x) : stk
exec1 ADD       _ (j:i:stk) = (i+j)       : stk 
exec1 _         _ _         = [] 

{-@ reflect exec @-}
exec :: [Instr] -> State -> Stack -> Stack 
exec []     _ stk = stk 
exec (i:is) s stk = exec is s (exec1 i s stk)


--------------------------------------------------------------------------------
-- | Compiling Arithmetic Expressions to a Stack Machine 
--------------------------------------------------------------------------------

{-@ reflect comp @-}
comp :: AExp -> [Instr]
comp (N n)        = [LOADI n]
comp (V x)        = [LOAD x]
comp (Plus a1 a2) = comp a1 ++ (comp a2 ++ [ADD])

{-@ lemma_comp :: a:_ -> s:_ -> stk:_ -> { exec (comp a) s stk = cons (aval a s) stk } @-}
lemma_comp :: AExp -> State -> Stack -> Proof 
lemma_comp (N n)        s stk = () 
lemma_comp (V x)        s stk = () 
lemma_comp (Plus a1 a2) s stk = lemma_exec_append (comp a1) (comp a2 ++ [ADD]) s stk
                            &&& lemma_exec_append (comp a2) [ADD] s stk1
                            &&& lemma_comp a1 s stk 
                            &&& lemma_comp a2 s stk1
  where 
    stk2                      = exec (comp a2) s stk1
    stk1                      = exec (comp a1) s stk

{-@ lemma_exec_append :: is1:_ -> is2:_ -> s:_ -> stk:_ -> 
      { exec (is1 ++ is2) s stk = exec is2 s (exec is1 s stk) }
  @-}
lemma_exec_append :: [Instr] -> [Instr] -> State -> Stack -> Proof
lemma_exec_append []       _   _ _   = () 
lemma_exec_append (i1:is1) is2 s stk = lemma_exec_append is1 is2 s (exec1 i1 s stk)