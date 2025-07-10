{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# OPTIONS_GHC -fwarn-incomplete-uni-patterns #-}

module TreeGrammars where

-- Corresponds to the definition in (5) on the handout
data Tree sy = Node sy [Tree sy] deriving Show

-- The following would be possible instead, but we're not doing it this way 
-- data Tree sy = Leaf sy | NonLeaf sy [Tree sy] -- this is ugly if the list of trees is empty

-- Corresponds to the tree in (7) on the handout
t7 :: Tree Char
t7 = Node 'b' [Node 'c' [Node 'a' []], Node 'a' [Node 'b' [], Node 'b' []]]

-- Corresponds to the definition in (10) on the handout
type TreeAutomaton st sy = ([st], [sy], [st], [([st],sy,st)])

--------------------------------------------------------------------------------
-- The example from section 2.4.1 on the handout

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
-- The example from section 2.4.3 on the handout

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

