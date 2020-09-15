--Scribe Notes for Feb. 8, 2019
--Scribe Name: Adrian Salguero


-- Relation = a subset of the combinations of two sets 
-- Example: the pairs of natural numbers where the first value is one less than its partner 

-- Relations
type Real a = a -> a -> Bool


-- The Predicate describing the closure of a relation
data Path a where
   Refl :: Rel a -> a -> Path a 
   Step :: Rel a -> a -> a -> a -> Path a -> Path a

{-@ data Path a where
      Refl :: r:Rel a -> x:a -> Prop (Path r x x)
    | Step :: r:Rel a -> x:a -> y:{a | r x y} -> z:a -> Prop (Path r y z) -> Prop (Path r x z)
  @-}



{-@ lemma_Path_trans :: r:Rel a -> x:a -> y:a -> z:a
      -> Prop (Path r x y)
      -> Prop (Path r y z)
      -> Prop (Path r x z)
  @-}

lemma_Path_trans :: Rel a -> a -> a -> a -> Path a -> Path a -> Path a
lemma_Path_trans r x y z (Refl _ _)          yz = yz
lemma_Path_trans r x y z (Step _ _ x1 _ x1y) yz = Step r x x1 z (lemma_Path_trans r x1 y z x1y yz)

-- From last time:

-- Inductive predicate that allows us to define to proof systems. The first example that we saw was that of proving even Peanos
-- We define Relation as the following:

Relation r :: a -> a -> Bool

-- We can think of relations as paths on a graph where an edge between two varaibles indicates a relation.
-- We can first describe the reflexive case as we can define a path to be from a variable on the graph to itself.
-- If we have a path from x to y and a path from y to z, then there must be a path from x to z. We will be proving this fact using the following lemmas.
-- x -> ... -> y
-- y -> ... -> z
-- Our first lemma is lemma_Path_trans which will be used to prove the transitive property.

-- Construct a path: x -> ... -> z

-- We want to do an induction on the first path (x -> y) 
{-@ lemma_Path_trans :: r:Rel a -> x:a -> y:a -> z:a
      -> Prop (Path r x y)
      -> Prop (Path r y z)
      -> Prop (Path r x z)
  @-}
lemma_Path_trans :: Rel a -> a 
-- We can case split on p_xy: We can construct a path in 2 different ways, using the Refl and Step cases seen above.


-- Case 1
-- Path : p_xy -> x = x
lemma_Path_trans r x y z (Refl mumble grumble) p_yz = p_yz 

-- How do we know that x == y at this point? 
-- p_xy (path from x to y)                          :: Prop (Path r x y) (We know this from the precondition)
-- We know from the properties of Refl it gives us a path from x -> x
-- p_xy == Refl mumble grumble => therefore it must be Prop (Path mumble grumble grumble)

-- It must be that r = mumble, x = grumble, y = grumble -> x == y
-- Note: We can replace mumble, grumble with _ _

-- Second case
-- Path : p_xy = x -> x1 -> ... -> y
-- p_xy                         :: Prop (Path r x y)
-- p_xy === Step r x x1 y p_x1y :: Prop (Path r x y)
-- p_x1y                        :: Prop (r x1 y)
-- p_yz                         :: Prop (Path r y z)


lemma_Path_trans r x y z (Step _r _x x1 _y p_x1y) p_yz = p_xz 
   where
      p_xz = Step r x x1 z p_x1z                    -- x -> x1 -> ... -> z 
      p_x1z = lemma_Path_trans r x1 y z p_x1y p_yz  -- Prop (Path r x1 z) (Call the lemma_Path_trans)
	  
	  
	  
-- Now we want to define a list to be a palindrome (Ex: racecar, 'a')
-- We define a palindrome on String
-- Predicate Pal xs = should denote the string 'xs' is a palindrome
-- How to define the function isPal :: String -> Bool? 

isPal :: (Eq a) => [a] -> Bool
isPal xs = xs == rev xs

-- We can also define this from scratch as a proof systems, similar to what we saw with the Even Peanos

-- Base Case: Empty string or single character String
{-

   ()
---------------------Pal0
   Pal[]


-------------------- Pal1
   Pal [x]


-- Inductive Step: Note that if we have a palindrome labeled 'l' then we can create a new palindrome if we append the string [x] to both sides of it

   Pal l 
-------------------------------------
   Pal ([x] # l # [x]) (makePal x l)


-}

--------------------------------------------------------------------------------
-- | The Prop declaring the Palindrome predicate 
data PalP a where
  Pal :: [a] -> PalP a

-- | The Predicate implementing the Palindrom predicate 
data Pal a where
  Pal0 :: Pal a 
  Pal1 :: a -> Pal a 
  Pals :: a -> [a] -> Pal a -> Pal a 

{-@ data Pal a where
      Pal0 :: Prop (Pal []) 
    | Pal1 :: x:_ -> Prop (Pal (single x)) 
    | Pals :: x:_ -> xs:_ -> Prop (Pal xs) -> Prop (Pal (mkPal x xs)) 
  @-}

{-@ reflect single @-}
single :: a -> [a]
single x = [x]

{-@ reflect mkPal @-}
mkPal :: a -> [a] -> [a]
mkPal x xs = x : (xs ++ [x])


-- Our goal is to prove xs == rev xs

{-@ ple lemma_pal @-}
{-@ lemma_pal :: xs:_ -> p:Prop (Pal xs) -> { xs == rev xs } @-}
lemma_pal :: [a] -> Pal a -> Proof
lemma_pal  = undefined

-- Case split on the list 

lemma_pal [] _ = ()
lemma_pal [x] _ = undefined
lemma_pal xs (Pal0 {}) = undefined -- impossible
lemma_pal xs (Pal1 {}) = undefined -- impossible


lemma_pal xs py@(Pals y ys pal_ys)
   = rev xs
   === rev (y : (ys ++ [y]))
   === rev (ys ++ [y]) ++ [y]
      ? lemma_rev_app ys [y]
   === (rev [y] ++ rev ys) ++ [y]
   === ([y] ++ rev ys) ++ [y]
      ? lemma_pal ys pal_ys 
   === ([y] ++ ys) ++ [y]
   === xs 

-- py :: Prop (Pal (mkPal y ys)) -- [y] ++ ys ++ [y]

-- It is also a proof of Pal xs
-- py :: Prop (Pal xs)
-- xs = y: (ys ++ [y])
-- pal_ys :: Prop (Pal ys) --> by IH --> ys == rev ys


