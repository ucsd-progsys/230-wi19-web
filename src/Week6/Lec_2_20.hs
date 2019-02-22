{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--diff"        @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

{-@ infixr ++  @-}  -- TODO: Silly to have to rewrite this annotation!

{-# LANGUAGE GADTs #-}

module Lec_2_20 where

import           Prelude hiding ((++)) 
import           ProofCombinators
import qualified State as S
import           Expressions hiding (And)
import           Imp 



-----------------------------------------------------------------------
-- Relations
type Rel a = a -> a -> Bool

-- | The Prop describing the closure of a relation
data PathProp a where
  Path :: Rel a -> a -> a -> PathProp a

-- | The Proof of the existence of a path ... 
data PathProof a where
  Refl :: Rel a -> a -> PathProof a
  Step :: Rel a -> a -> a -> a -> PathProof a -> PathProof a

{-@ data PathProof a where
      Refl :: r:Rel a -> x:a -> Prop (Path r x x)
    | Step :: r:Rel a -> x:a -> y:{a | r x y} -> z:a -> Prop (Path r y z) -> Prop (Path r x z)
  @-}

--------------------------------------------------------------------------------

-- x -> ... -> y        y -> ... -> z
--------------------------------------
-- x -> ... -> z



--------------------------------------------------------------------------------
-- | Defining "Even Numbers"
--------------------------------------------------------------------------------

data Peano = Z | S Peano

-- | The "Prop" describing an Even number `(Ev n)`

data EvProp where
  Ev :: Peano -> EvProp

-- | The ways to "construct evidence" of evenness i.e. that "prove" `Ev n`

data EvProof where
  EvZ :: EvProof
  EvS :: Peano -> EvProof -> EvProof

-- 
-- type Prop E = {v:_ | prop v = E}

{-@ data EvProof where
      EvZ :: Prop (Ev Z)
    | EvS :: n:Peano -> Prop (Ev n) -> Prop (Ev (S (S n)))
  @-}

{- | Read the above as there are two "rules" to determine even-ness


      ------------------ [EvZ]
         Ev Z


         Ev n
      ------------------ [EvS]
         Ev (S (S n))

 -}

{-@ zero_is_Even :: {pf:EvProof | prop pf == (Ev Z) } @-}
zero_is_Even :: EvProof 
zero_is_Even = EvZ

{-@ two_is_Even :: {pf : EvProof | prop pf = (Ev (S (S Z))) } @-}
two_is_Even :: EvProof  
two_is_Even = EvS Z zero_is_Even

{-@ four_is_Even :: Prop (Ev (S (S (S (S Z))))) @-}
four_is_Even :: EvProof  
four_is_Even = EvS (S (S Z)) two_is_Even



--------------------------------------------------------------------------------
-- | Big-step Semantics 
--------------------------------------------------------------------------------

{- BIG Step Semantics 

  BStep c s s'


  ------------------[BSkip]
    BStep Skip s s


  ------------------------------------------[BAssign]
    BStep (x := a) s (set s x (aval a s))


    BStep c1 s smid    BStep c2 smid s'
  ----------------------------------------[BSeq]
    BStep (c1; c2) s s' 


    bval b s = TRUE      BStep c1 s s'
  ----------------------------------------[BIfT]
    BStep (If b c1 c2) s s' 


    bval b s = FALSE     BStep c2 s s'
  ----------------------------------------[BIfF]
    BStep (If b c1 c2) s s' 


    bval b s = TRUE      
    BStep c s smid  
    BStep (While b c) smid s'   
  --------------------------------------------------[BWhileT]
    BStep (While b c) s s' 

    bval b s = FALSE      
  ----------------------------------------[BWhileF]
    BStep (While b c) s s

 -}


data BStepProp where
  BStep :: Com -> State -> State -> BStepProp 

data BStepProof where 
  BSkip   :: State -> BStepProof 
  BAssign :: Vname -> AExp -> State -> BStepProof 
  BSeq    :: Com   -> Com  -> State -> State -> State -> BStepProof -> BStepProof -> BStepProof 
  BIfT    :: BExp  -> Com  -> Com   -> State -> State -> BStepProof -> BStepProof  
  BIfF    :: BExp  -> Com  -> Com   -> State -> State -> BStepProof -> BStepProof
  BWhileF :: BExp  -> Com  -> State -> BStepProof 
  BWhileT :: BExp  -> Com  -> State -> State -> State -> BStepProof -> BStepProof -> BStepProof 

{-@ data BStepProof where 
      BSkip   :: s:_ 
              -> Prop (BStep Skip s s)
    | BAssign :: x:_ -> a:_ -> s:_
              -> Prop (BStep (Assign x a) s (asgn x a s)) 
    | BSeq    :: c1:_ -> c2:_ -> s1:_ -> s2:_ -> s3:_
              -> Prop (BStep c1 s1 s2) 
              -> Prop (BStep c2 s2 s3) 
              -> Prop (BStep (Seq c1 c2) s1 s3)
    | BIfT    :: b:_ -> c1:_ -> c2:_ -> s:{_ | bval b s} -> s1:_
              -> Prop (BStep c1 s s1) 
              -> Prop (BStep (If b c1 c2) s s1)
    | BIfF    :: b:_ -> c1:_ -> c2:_ -> s:{_ | not (bval b s)} -> s2:_ 
              -> Prop (BStep c2 s s2) 
              -> Prop (BStep (If b c1 c2) s s2)
    | BWhileF :: b:_ -> c:_ -> s:{_ | not (bval b s)} 
              -> Prop (BStep (While b c) s s)
    | BWhileT :: b:_ -> c:_ -> s1:{_ | bval b s1} -> s1':_ -> s2:_
              -> Prop (BStep c s1 s1') 
              -> Prop (BStep (While b c) s1' s2)
              -> Prop (BStep (While b c) s1 s2)
  @-}  


--------------------------------------------------------------------------------

-- x := 5
{-@ reflect cmd_1 @-}
cmd_1 = "x" <~ N 5

-- y := x
{-@ reflect cmd_2 @-}
cmd_2 = "y" <~ (V "x")

-- x := 5; y := x
{-@ reflect cmd_1_2 @-}
cmd_1_2 = cmd_1 @@ cmd_2 

{-@ reflect prop_set @-}
prop_set cmd x v s = BStep cmd s (S.set s x v)


-- BStep (x := 5) s (S.set s x 5)
{-@ step_1 :: s:State -> Prop (BStep (Assign {"x"} (N 5)) s (S.set s {"x"} 5)) @-}
step_1 s =  BAssign "x" (N 5) s



{-@ step_2 :: s:{State | S.get s "x" == 5} -> Prop (prop_set cmd_2 {"y"} 5 s) @-}
step_2 s = BAssign "y" (V "x") s

{-@ step_1_2 :: s:State -> Prop (BStep cmd_1_2 s (S.set (S.set s {"x"} 5) {"y"} 5)) @-}
step_1_2 s = BSeq cmd_1 cmd_2 s s1 s2 (step_1 s) (step_2 s1) 
  where 
    s1     = S.set s  "x" 5 
    s2     = S.set s1 "y" 5

{- 
{-@ lem_semi :: c1:_ -> c2:_ -> c3:_ -> s:_ -> s3:_
      -> Prop (BStep (Seq (Seq c1 c2) c3) s s3)
      -> Prop (BStep (Seq c1 (Seq c2 c3)) s s3) 
  @-}
lem_semi :: Com -> Com -> Com -> State -> State -> _ -> _
lem_semi _ _ _ s s3 (BSeq c12 c3 _ s2 _ (BSeq c1 c2 _ s1 _  bs1 bs2) bs3) 
  = BSeq c1 (Seq c2 c3) s s1 s3 bs1 (BSeq c2 c3 s1 s2 s3 bs2 bs3)

-}