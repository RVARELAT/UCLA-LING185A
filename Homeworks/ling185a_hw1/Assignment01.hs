module Assignment01 where

-- Imports everything from the Recursion module. 
import Recursion
import FiniteState

-- Another type that gives us something vaguely linguistic to play with,
-- which we'll use as symbols for some FSAs
data SegmentPKIU = P | K | I | U | MB deriving (Show,Eq)

-- Checks that all states and symbols mentioned in the transition 
-- table (i.e. delta) come from the provided lists of states and symbols.
fsaSanityCheck :: (Eq a) => Automaton a -> Bool
fsaSanityCheck m =
    let (states, syms, i, f, delta) = m in
    let validTransition (q1,x,q2) = elem q1 states && elem x syms && elem q2 states in
    and (map validTransition delta)

------------------------------------------------------------------
------------------------------------------------------------------
-- IMPORTANT: Please do not change anything above here.
--            Write all your code below this line.


-- Please submit your answer of Part 1 and Part 5B as a pdf on BruinLearn. 

-- helper function for depth function
maxNumber :: Numb -> (Numb -> Numb)
-- both nums are zero
maxNumber Z Z = Z
-- either num is 0 (return the other num)
maxNumber n1 Z = n1
maxNumber Z n2 = n2
maxNumber (S num1) (S num2) = S (maxNumber num1 num2)

----------Section 2
depth :: Form -> Numb
-- leaf Nodes
depth T = S Z
depth F = S Z
depth (Neg rest) = S (depth rest)
-- use maxNumber to find max of left and right subtree
depth (Cnj left right) = S (maxNumber (depth left) (depth right))
depth (Dsj left right) = S (maxNumber (depth left) (depth right))


countNegs :: Form -> Numb
-- For T and F we get Zero (No negs to add)
countNegs T = Z
countNegs F = Z
-- found a Neg so add one S
countNegs (Neg rest) = S (countNegs rest)
-- add Negs on left and right subtrees using add function (if any)
countNegs (Cnj left right) = otherAdd (countNegs left) (countNegs right)
countNegs (Dsj left right) = otherAdd (countNegs left) (countNegs right)


----------Section 3
multiply :: Numb -> (Numb -> Numb)
multiply = \num1 -> \num2 -> case num1 of 
                    Z -> Z
                    S n' -> otherAdd num2 (multiply n' num2)


isEqual :: Numb -> (Numb -> Bool)
-- Base Case: both are zero
isEqual Z Z = True
-- one is zero and other is not
isEqual (S Z) Z = False
isEqual Z (S Z) = False
-- peel off one S from each number
isEqual (S n) (S m) = isEqual n m
 

---------Section 4

listOf :: Numb -> (a -> [a])
-- return an empty list when list of length zero
listOf Z x = []
-- x is the element we want to add to the list
listOf (S n) x = x : listOf n x

addToEnd :: a -> ([a] -> [a])
-- put element x in empty list
addToEnd newElement [] = [newElement]
-- Keep adding the original elements into the list until we add the new one add the end
addToEnd newElement (y:rest) = y : addToEnd newElement rest


reverseL :: [a] -> [a]
-- empty list returns an empty list
reverseL [] = []
reverseL (y:rest) = addToEnd y (reverseL rest)


-- helper to check if letter is a vowel
vowel :: SegmentPKIU -> Bool
vowel U = True
vowel I = True
vowel x = False

adjacentVowels :: [SegmentPKIU] -> Bool
-- empty list
adjacentVowels [] = False
-- one element in list
adjacentVowels [x] = False
adjacentVowels (left:right:rest) =
    case vowel left of
        -- left letter is a vowel
        True -> case vowel right of
            -- right letter is a vowel
            True -> True
            -- right letter is not a vowel (check rest of list)
            False -> adjacentVowels (right:rest)
        -- left letter is not a vowel (check rest of list)
        False -> adjacentVowels (right:rest)


--------Section 5

fsa_countCs::Automaton SegmentCV
fsa_countCs = ([20,51,13,48], [C,V], [20], [48], [(20, V, 20),
                                                   (20, C, 51),

                                                   (51, V, 51),
                                                   (51, C, 13),

                                                   (13, V, 13),
                                                   (13, C, 20),
                                                   (13, C, 48),

                                                   (48, V, 48)])

-- check part 5b
fsa_twoVs::Automaton SegmentCV
fsa_twoVs = ([1,2,3], [C,V], [1], [3], [(1, V, 1),
                                        (1, C, 1),
                                        (1, V, 2),

                                        (2, C, 2),
                                        (2, V, 3),

                                        (3, C, 3),
                                        (3, V, 3)])




