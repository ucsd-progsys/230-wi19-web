{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--diff"        @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

{-@ infixr ++  @-}  -- TODO: Silly to have to rewrite this annotation!

{-# LANGUAGE GADTs #-}

module Lec_2_11 where 

import           Prelude hiding ((++)) 
import           ProofCombinators
import           Lists 
import qualified State as S
import           Expressions hiding (And)

--------------------------------------------------------------------------------
{- Boolean Expressions 

data BExp 
  = Bc   Bool 
  | Not  BExp 
  | And  BExp BExp 
  | Less AExp AExp  

-}

--------------------------------------------------------------------------------
-- | IMP Commands
--------------------------------------------------------------------------------

data Com 
  = Skip 
  | Assign Vname AExp 
  | Seq    Com   Com 
  | If     BExp  Com   Com 
  | While  BExp  Com 
  deriving (Show)


