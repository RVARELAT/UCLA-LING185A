{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# OPTIONS_GHC -fwarn-incomplete-uni-patterns #-}

module FinalUtilities where

import Control.Applicative(liftA, liftA2, liftA3)
import Data.List(nub)
import Data.List(lookup)

-------------------------------------------------------------------------
-----------------------------Set up for Section 1 -----------------------
-------------------------------------------------------------------------

-- A list-like type that will be useful for computing forward values
data SnocList a = ESL | (SnocList a) ::: a deriving Show

-- The word ``hello'' encoded as a snoc list of characters
sl :: SnocList Char
sl = ((((ESL ::: 'h') ::: 'e') ::: 'l') ::: 'l') ::: 'o'


-- Some types we'll use for the symbols of some FSAs. 
-- By ``deriving Eq'' we are linking the default/obvious 
-- equality function on this type to the name (==).
data SegmentCV = C | V deriving (Show, Eq)
data SegmentPKIU = P | K | I | U | MB deriving (Show,Eq)


-- This is a parametrized type synonym: it defines `Automaton st sy' as a 
-- type that we'll use to represent an FSA with symbols of type sy and states of type st. 
-- So `Automaton Int SegmentCV' is a type for FSAs with symbols of type SegmentCV and states of type Int. 
type Automaton st sy = ([st], [sy], [st], [st], [(st,sy,st)])

-- Here's the FSA from (4) on Lecture 2 Handout.
fsa_handout4 :: Automaton Int SegmentCV
fsa_handout4 = ([40,41,42,43], [C,V], [40], [43], [(40, C, 40),
                                                   (40, V, 40),
                                                   (40, C, 41),
                                                   (40, V, 42),
                                                   (41, C, 43),
                                                   (42, V, 43),
                                                   (43, C, 43),
                                                   (43, V, 43)])

-- Here's the FSA from (5) on the Lecture 2 handout
fsa_handout5 :: Automaton Int SegmentCV
fsa_handout5 = ([1,2,3], [C,V], [1], [3], [(1, C, 1),
                                           (1, V, 1),
                                           (1, V, 2),
                                           (2, C, 3)])

-- Here's the FSA from (6) on the Lecture 2 handout
fsa_handout6 :: Automaton Int SegmentCV
fsa_handout6 = ([1,2,3], [C,V], [1], [1], [(1, V, 1), (1, C, 2), (1, V, 3), 
                                           (2, V, 1), (2, V, 3), 
                                           (3, C, 1)])


-- Corresponds to the definition of semiring-valued FSAs. 
-- parametrized by type of state and type of symbols
-- also parametrized with values associated with each transition/string
-- For a Boolean FSA, v would be Bool
type GenericAutomaton st sy v = ([st], [sy], st -> v, st -> v, (st,sy,st) -> v)


-- Again, feel free to ignore the details of this function.
-- What the function does is to fill out all other transitions that are not specified out with the value of the first argument. 
makeGFSA :: (Eq st, Eq sy) => v -> ([st], [sy], [(st,v)], [(st,v)], [((st,sy,st),v)]) -> GenericAutomaton st sy v
makeGFSA def (states, syms, starts, ends, transitions) =
    let mylookup l x = case lookup x l of {Just y -> y; Nothing -> def} in
    (states, syms, mylookup starts, mylookup ends, mylookup transitions)


gfsa5 :: GenericAutomaton Int Char Bool
gfsa5 = makeGFSA False ([1,2,3], ['C','V'],
                         [(1, True)], [(1, True)], 
                         [((1,'V',1), True),
                          ((1,'C',2), True),
                          ((1,'V',3), True),
                          ((2,'V',1), True),
                          ((2,'V',3), True),
                          ((3,'C',1), True)])

gfsa6 :: GenericAutomaton Int Char Float
gfsa6 = makeGFSA 0 ([1,2,3], ['C','V'],
                    [(1, 1.0)], 
                    [(1, 1.0)], 
                    [((1,'V',1), 0.9),
                     ((1,'C',2), 1.0),
                     ((1,'V',3), 0.9),
                     ((2,'V',1), 1.0),
                     ((2,'V',3), 1.0),
                     ((3,'C',1), 0.8)])

gfsa23 :: GenericAutomaton Int Char Double
gfsa23 = makeGFSA 0 ([1,2,3], ['C','V'],
                    [(1, 1.0)], 
                    [(1, 0.1)], 
                    [((1,'V',1), 0.2),
                     ((1,'C',2), 0.5),
                     ((1,'V',3), 0.2),
                     ((2,'V',1), 0.5),
                     ((2,'V',3), 0.5),
                     ((3,'C',1), 1.0)])

data Cost = TheInt Int | Inf deriving Show

-- Cost-weighted FSA from (32) on the handout
gfsa32 :: GenericAutomaton Int Char Cost
gfsa32 = makeGFSA Inf ([1,2,3], ['C','V'],
                       [(1, TheInt 0)], [(1, TheInt 0)], 
                       [((1,'V',1), TheInt 1),
                        ((1,'C',2), TheInt 0),
                        ((1,'V',3), TheInt 1),
                        ((2,'V',1), TheInt 0),
                        ((2,'V',3), TheInt 0),
                        ((3,'C',1), TheInt 2)])

----------------------------------------------------------
-- Setting up the semiring type class.

-- This says, ``Some types are semiring types. To be a semiring 
-- type you need to have two two-place operations called `&&&' and 
-- `|||', and two elements called `gtrue' and `gfalse'.''
class Semiring a where
    (&&&) :: a -> a -> a
    (|||) :: a -> a -> a
    gtrue :: a
    gfalse :: a

-- This says, ``Bool is a semiring type. When some code 
-- based on semirings uses `x &&& y', what that means for 
-- the type Bool is `x && y'; when some semiring code uses 
-- `x ||| y', what that means for Bool is `x || y'; etc.''
instance Semiring Bool where
    x &&& y = x && y
    x ||| y = x || y
    gtrue = True
    gfalse = False

-- Similarly for the Float type. 
-- When some code based on semirings uses `x &&& y', what 
-- that means for the type Float is `x * y'; etc.
instance Semiring Float where
    x &&& y = x * y
    x ||| y = max x y
    gtrue = 1.0
    gfalse = 0.0

-- Similarly for the Double type. 
-- When some code based on semirings uses `x &&& y', what 
-- that means for the type Double is `x * y'; etc.
instance Semiring Double where
    x &&& y = x * y
    x ||| y = x + y
    gtrue = 1.0
    gfalse = 0.0

----------------------------------------------------------
-- Some functions that will be usable with any semiring
---In this way, we don't have to create separate machinery 
-- to data with Bools or data with Doubles for example. 
gen_or :: Semiring a => [a] -> a
gen_or list =
    case list of
    [] -> gfalse
    (x:xs) -> x ||| (gen_or xs)

-- For boolean typed lists, this is the same as: 
--gen_or :: [Bool] -> a
--gen_or list =
--    case list of
--    [] -> False
--    (x:xs) -> x || (gen_or xs)

gen_and :: Semiring a => [a] -> a
gen_and list =
    case list of
    [] -> gtrue
    (x:xs) -> x &&& (gen_and xs)



-------------------------------------------------------------------------
---------------------------Setup for Section 2---------------------------
-------------------------------------------------------------------------

type SLG sy = ([sy], [sy], [sy], [(sy,sy)])
data ConstructedState sy = ExtraState | StateForSymbol sy deriving (Eq, Show)

slg1 :: SLG SegmentCV
slg1 = ([C,V], [C], [V], [(C,C),(C,V),(V,V)])

slg2 :: SLG Int
slg2 = ([1,2,3], [1,2,3], [1,2,3], [(1,1),(2,2),(3,3),(1,2),(2,1),(1,3),(3,1)])


data SyllableTypes = Stressed | Unstressed deriving (Eq, Show)

----------------------------------------------------------------------------
-- Basic generation for FSAs

backward :: (Eq st, Eq sy) => Automaton st sy -> [sy] -> st -> Bool
backward m w q =
    let (states, syms, i, f, delta) = m in
    case w of
    [] -> elem q f
    (x:rest) -> or (map (\q1 -> elem (q,x,q1) delta && backward m rest q1) states)

generates :: (Eq st, Eq sy) => Automaton st sy -> [sy] -> Bool
generates m w =
    let (states, syms, i, f, delta) = m in
    or (map (\q0 -> elem q0 i && backward m w q0) states)
--------------------------------------------------------------------------
---------------------------Setup for Section 4----------------------------
--------------------------------------------------------------------------

data Tree sy = Node sy [Tree sy] deriving Show
type TreeAutomaton st sy = ([st], [sy], [st], [([st],sy,st)])


--------------------------------------------------------------------------------
-- The example from section 2.4.1 on the Lecture 10 handout
t14 :: Tree Char
t14 = Node 'a' [Node 'b' [Node 'b' [Node 'a' []], Node 'a' [Node 'b' [], Node 'a' []]]]

data Parity = Even | Odd deriving (Show,Eq)

fsta_even :: TreeAutomaton Parity Char
fsta_even = ([Even,Odd], ['a','b'], [Even],
             [ ([Even,Even], 'a', Odd),     ([Even,Even], 'b', Even), 
               ([Even,Odd],  'a', Even),    ([Even,Odd],  'b', Odd), 
               ([Odd,Even],  'a', Even),    ([Odd,Even],  'b', Odd), 
               ([Odd,Odd],   'a', Odd),     ([Odd,Odd],   'b', Even), 
               ([Even],      'a', Odd),     ([Even],      'b', Even), 
               ([Odd],       'a', Even),    ([Odd],       'b', Odd), 
               ([],          'a', Odd),     ([],          'b', Even)
             ])

--------------------------------------------------------------------------------
-- The example from section 2.4.3 on the Lecture 10 handout

t20 :: Tree String
t20 =
    Node "*" [
        Node "*" [
            Node "that" [], 
            Node "*" [ Node "nobody" [], Node "*" [Node "met" [], Node "anybody" []] ]
        ] ,
        Node "*" [Node "surprised" [], Node "John" [] ]
    ]

data NegStatus = Neg | Lic | Zero deriving (Show,Eq)

fsta_npi :: TreeAutomaton NegStatus String
fsta_npi = let npis = ["anybody", "ever"] in
           let licensors = ["nobody", "not"] in
           let otherwords = ["that", "met", "surprised", "John"] in
           ([Zero, Lic, Neg],
            ["*"] ++ npis ++ licensors ++ otherwords,
            [Zero, Lic],
            [([Neg, Neg], "*", Neg), 
             ([Zero, Neg], "*", Neg), 
             ([Neg, Zero], "*", Neg), 
             ([Zero, Zero], "*", Zero), 
             ([Lic, Neg], "*", Zero), 
             ([Lic, Zero], "*", Zero), 
             ([Zero, Lic], "*", Zero), 
             ([Lic, Lic], "*", Zero)
            ] ++ map (\s -> ([], s, Zero)) otherwords 
              ++ map (\s -> ([], s, Lic)) licensors
              ++ map (\s -> ([], s, Neg)) npis
           )



------------------------------------------------------
-- Some tiny helpers for writing trees more compactly

lf :: a -> Tree a
lf x = Node x []

mrg :: Tree String -> Tree String -> Tree String
mrg t1 t2 = Node "*" [t1,t2]

------------------------------------------------------

-- (1a)/(2a) `C John ate an apple yesterday'
tree_1a :: Tree String
tree_1a = mrg (lf "C") (mrg (lf "John") (mrg (mrg (lf "ate") (mrg (lf "an") (lf "apple"))) (lf "yesterday")))

-- (1b)/(2b) `Q John ate what yesterday'
tree_1b :: Tree String
tree_1b = mrg (lf "Q") (mrg (lf "John") (mrg (mrg (lf "ate") (lf "what")) (lf "yesterday")))

-- (3a) `Q John ate an apple yesterday'
tree_3a :: Tree String
tree_3a = mrg (lf "Q") (mrg (lf "John") (mrg (mrg (lf "ate") (mrg (lf "an") (lf "apple"))) (lf "yesterday")))

-- (3b) `C John ate what yesterday'
tree_3b :: Tree String
tree_3b = mrg (lf "C") (mrg (lf "John") (mrg (mrg (lf "ate") (lf "what")) (lf "yesterday")))

tree_13 :: Tree String
tree_13 =
    Node "*" [
        Node "Q" [],
        Node "*" [
            Node "John" [],
            Node "*" [
                Node "laughed" [],
                Node "**" [
                    Node "because" [],
                    Node "*" [
                        Node "Mary" [],
                        Node "*" [
                            Node "*" [Node "bought" [], Node "books" []],
                            Node "why" []
                        ]
                    ]
                ]
            ]
        ]
    ]
