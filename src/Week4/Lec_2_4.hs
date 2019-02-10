{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--diff"       @-}
{-@ LIQUID "--ple"        @-}
{-@ infixr ++  @-}  -- TODO: Silly to have to rewrite this annotation!

{-# LANGUAGE GADTs #-}

module Lec_2_4 where

import           Prelude hiding ((++)) 
import           ProofCombinators 
import           Lists 
import           Expressions 
import qualified State as S 


data Peano where 
  Z :: Peano 
  S :: Peano -> Peano 


-- How to define "Even"?

{-@ reflect isEven @-}
isEven :: Peano -> Bool 
isEven Z     = True 
isEven (S n) = not (isEven n) 


-- (isEven k)

-- (isWellTyped p)

-- 1. define "div-by-2" or "mod-2"
-- 2. define it recursively on the peano 
-- 3. "recur" 
-- 4. make a NEW type

----
{- 
    data List a = Nil | Cons a (List a)
   
    data List a where 

        Nil  :: List a
        Cons :: a -> List a -> List a

-}
----
-- | The "Prop" describing an Even number `(Ev n)`

data EvP where
  Ev :: Peano -> EvP

{-@ data Ev where
      EvZ :: Prop (Ev Z) 
    | EvS :: n:Peano -> Prop (Ev n) -> Prop (Ev (S (S n))) 
  @-}

data Ev where
  EvZ :: Ev 
  EvS :: Peano -> Ev -> Ev 

{-@ zero_is_Even :: Prop (Ev Z) @-}
zero_is_Even :: Ev 
zero_is_Even = EvZ 

{-@ two_is_Even :: Prop (Ev (S (S Z))) @-}
two_is_Even :: Ev 
two_is_Even = EvS Z EvZ 

{-@ four_is_Even :: Prop (Ev (S (S (S (S Z))))) @-}
four_is_Even :: Ev 
four_is_Even = EvS (S (S Z)) two_is_Even 


{- 
   
-- WHY IS this even Even?

    EvZ && EvS (S (S Z))

        but EvS takes TWO parameters so ...

    EvS Z EvZ 
    
        'proof that n is Even' 

 -}


-- | Q: Have we really defined Ev? 

-- n:_ -> isEven n -> Prop (Ev n)
-- n:_ ->  Prop (Ev n) -> isEven n 
d


dummy :: Int
dummy = 10 
