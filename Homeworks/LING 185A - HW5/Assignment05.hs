{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# OPTIONS_GHC -fwarn-incomplete-uni-patterns #-}

module Assignment05 where

import Control.Applicative(liftA, liftA2, liftA3)

import TreeGrammars

plainWords = ["John","Mary","ate","bought","an","apple","books","yesterday","C","laughed","because"]
whWords = ["who","what","why"]
qWords = ["Q"]

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

------------------------------------------------------------------
------------------------------------------------------------------
-- IMPORTANT: Please do not change anything above here.
--            Write all your code below this line.


----- 1. Working with trees (10 points)

-----1A; please put your answer to question 1A as a comment down here. 

-- The function creates a list of all the symbols in a tree that are leaf nodes from left-to-right. 
 

-----1B & 1C
total :: (Eq a) => a -> Tree a -> Int
total given_symbol (Node x daughters) = case daughters of
    -- no daughters (check if node x is the symbol)
    [] -> if x == given_symbol then 1 else 0
    -- The tree has daughters (check if current node matches symbol and then recursively apply 'total' to rest of daughters in tree)
    (t : rest) -> (if x == given_symbol then 1 else 0) + sum (map (total given_symbol) daughters)



leftmost :: Tree a -> [a]
leftmost (Node x daughters) = case daughters of
    -- no daughters (add node x to list)
    [] -> [x]
    -- Tree has daughters so add node x to list and then recursively call 'leftmost' on leftmost daughter
    (t : rest) -> x : leftmost t



----2
allLists :: Int -> [a] -> [[a]]
allLists given_length given_list = case given_length of 
    0 -> [[]]
    -- int greater than 0 (asssume non-negative)
    positiveNum -> [t : rest | t <- given_list, rest <- allLists (given_length - 1) given_list]

under :: (Eq st, Eq sy) => TreeAutomaton st sy -> Tree sy -> st -> Bool
under (states, symbols, endingStates, transitions) (Node symbol daughters) stateGoal =
    case daughters of
    -- check if transitions exists in list of transitons when no daughters in tree
    [] -> elem ([], symbol, stateGoal) transitions
    -- for all daughter states
    not_empty -> any (\daughter_states ->
            elem (daughter_states, symbol, stateGoal) transitions
            && and (zipWith (under (states, symbols, endingStates, transitions)) daughters daughter_states))
        (allLists (length daughters) states)



generatesFSTA :: (Eq st, Eq sy) => TreeAutomaton st sy -> Tree sy -> Bool
generatesFSTA (states, symbols, endingStates, transitions) tree = 
    case endingStates of
        -- can't reach final states
        [] -> False
        -- check if ending state can be reached (check all ending states) using under function
        (endState : rest) -> under (states, symbols, endingStates, transitions) tree endState || generatesFSTA (states, symbols, rest, transitions) tree




----3 
---A1

data WhState = None | Q_encountered | WH_encountered | C_encountered | Both_encountered deriving (Eq, Show)

fsta_wh :: TreeAutomaton WhState String
fsta_wh = let qWords = ["Q"] in
    let plainWords = ["John","Mary","ate","bought","an","apple","books","yesterday","C","laughed","because"] in
    let whWords = ["what", "who", "why"] in
    -- states
    ([None, Q_encountered, WH_encountered, C_encountered, Both_encountered],
    -- alphabet
    plainWords ++ whWords ++ qWords ++ ["*"],
    -- ending states
    [Both_encountered],
    -- transitions
    [([WH_encountered, WH_encountered], "*", WH_encountered),
     ([None, WH_encountered], "*", WH_encountered),
     ([WH_encountered, None], "*", WH_encountered),
     ([None, None], "*", None),
     -- Q c-commands WH
     ([Q_encountered, WH_encountered], "*", Both_encountered),
     ([Q_encountered, None], "*", None),
     ([None, Q_encountered], "*", None),
     ([Q_encountered, Q_encountered], "*", None),
     ([], "C", C_encountered),
     -- special case for "plain" complementizers 
     ([C_encountered, None], "*", Both_encountered)
    ] ++ map (\s -> ([], s, Q_encountered)) qWords
      ++ map (\s -> ([], s, WH_encountered)) whWords
      ++ map (\s -> ([], s, None)) plainWords
    )



----A2 Write a brief explanation (in plain English) of your states and your transition table: how did you set this
------------up in order to enforce the rules above? Put your answer as comments

-- States:
-- None - This state indicates we have not encountered anything "special" (C, Q, or WH), it's like a "neutral state"
-- Q-encountered - This state indicates we have encountered a Q complementizer in our tree (input)
-- WH-encountered - This state indicates we have encountered a WH-word in our tree (input)
-- C-encountered - This state indictates we have encountered a C complementizer in our tree (input)
-- both-encountered - This state indicates that both a Q-word and a WH-word have been encountered

-- Transition Table:
-- the transtion '[Q_encountered, WH_encountered], "*", Both_encountered)' handles the restriction that every Q must c-command at least one wh-word which is why we we have 'Q_encountered' on the left and 'WH_encountered' on the right and not vice versa. 
-- moreover the transition '([WH_encountered, WH_encountered], "*", WH_encountered)' allows the automaton to have multiple WH-words that can be c-commanded by a Q-complementizer
-- The transitions '([Q_encountered, None], "*", None), ([None, Q_encountered], "*", None), ([Q_encountered, Q_encountered], "*", None)' resests the state back to 'none' as we can only have one Q-complementizer and that can only c-command a wh-word
-- this special case transition '([C_encountered, None], "*", Both_encountered) is for trees like tree_1a that have a "plain" complementizer






