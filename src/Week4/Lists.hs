{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module Lists where 

import Prelude hiding ((++))
import ProofCombinators

-- data [a] = [] | a : List a 
--   deriving (Eq, Show)

{-@ reflect cons @-}
cons :: a -> [a] -> [a]
cons x xs = x : xs 

{-@ infixr ++  @-}
{-@ reflect ++ @-}
(++) :: [a] -> [a] -> [a] 
[]     ++ ys = ys 
(x:xs) ++ ys = x : (xs ++ ys)

{-@ reflect rev @-}
rev :: [a] -> [a] 
rev []     = [] 
rev (x:xs) = rev xs ++ [x] 

{-@ lemma_app_assoc :: xs:_ -> ys:_ -> zs:_ -> 
      { (xs ++ ys) ++ zs = xs ++ (ys ++ zs) } @-} 
lemma_app_assoc :: [a] -> [a] -> [a] -> Proof 
lemma_app_assoc []     _  _  = () 
lemma_app_assoc (_:xs) ys zs = lemma_app_assoc xs ys zs

{-@ lemma_app_Nil2 :: xs:_ -> { xs ++ [] = xs } @-}
lemma_app_Nil2 :: [a] -> Proof 
lemma_app_Nil2 []     = ()
lemma_app_Nil2 (x:xs) = lemma_app_Nil2 xs 

{-@ lemma_rev_app :: xs:_ -> ys:_ -> { rev (xs ++ ys) = rev ys ++ rev xs} @-}
lemma_rev_app :: [a] -> [a] -> Proof 

lemma_rev_app []     ys = lemma_app_Nil2 (rev ys)
lemma_rev_app (x:xs) ys = lemma_rev_app xs ys 
                      &&& lemma_app_assoc (rev ys) (rev xs) [x]

{-@ theorem_rev_rev :: xs:_ -> { rev (rev xs) = xs } @-}
theorem_rev_rev :: [a] -> Proof 
theorem_rev_rev []     = ()
theorem_rev_rev (x:xs) = lemma_rev_app (rev xs) [x]
                     &&& theorem_rev_rev xs 

