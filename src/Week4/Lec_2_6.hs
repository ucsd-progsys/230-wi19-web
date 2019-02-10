{-@ LIQUID "--reflection" @-}
{- LIQUID "--diff"       @-}
{-@ LIQUID "--ple"        @-}
{-@ infixr ++  @-}  -- TODO: Silly to have to rewrite this annotation!

{-# LANGUAGE GADTs #-}

module Lec_2_6 where

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
isEven Z         = True 
isEven (S n)     = not (isEven n)
-- isEven (S Z)     = False 
-- isEven (S (S n)) = isEven n 

-- (isEven k)

-- (isWellTyped p)

-- 1. define "div-by-2" or "mod-2"
-- 2. define it recursively on the peano 
-- 3. "recur" 
-- 4. make a NEW type


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
two_is_Even = EvS Z zero_is_Even 

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


{-@ lem_isEven :: n:_ ->  Prop (Ev n) -> { isEven n }  @-}
lem_isEven :: Peano -> Ev -> Proof 
lem_isEven Z     _              = () 
lem_isEven (S Z) EvZ            = () -- impossible "haha"
lem_isEven (S Z) (EvS _ _)      = () -- impossible "haha"
-- lem_isEven (S (S m))  EvZ       = () -- undefined 
lem_isEven (S (S m))  (EvS _m ev_m) =   isEven (S (S m)) 
                                    === not (not (isEven m))
                                    === isEven m 
                                      ? lem_isEven m ev_m 
                                    === True 
                                    *** QED 

-- "call  'lem_isEven m ev_m' ===> 'isEven m'

{-@ lemon :: n:{_| isEven n} -> Prop (Ev n) @-}
lemon :: Peano -> Ev 
lemon Z         = EvZ
lemon (S Z)     = impossible "asdasdasd" -- impossible "asdasd" 
-- lemon (S (S mm)) = EvS mm (lemon mm) 
lemon (S m)     = case m of 
                    Z    -> impossible "are you clever?" 
                    S mm -> EvS mm (lemon mm) 







{-@ lemma_ev :: n:_ -> Prop (Ev n) -> {isEven n} @-} 
lemma_ev :: Peano -> Ev -> Proof 
lemma_ev Z          _         = () 
lemma_ev (S Z)      EvZ       = () 
lemma_ev (S (S n)) (EvS _ pn) = lemma_ev n pn  
lemma_ev _ _ = impossible "hoho" 



dummy :: Int
dummy = 10 