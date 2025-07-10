{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant bracket" #-}
module Assignment02 where

import Prelude hiding (Either(..))

import Control.Applicative(liftA, liftA2, liftA3)
import Data.List(nub)

import FiniteStatePart2

---------------------------------------
-- Setup for section 3

data Either a b = First a | Second b deriving (Show,Eq)

re1 :: RegExp Char
re1 = Concat (Alt (Lit 'a') (Lit 'b')) (Lit 'c')

re2 :: RegExp Char
re2 = Star re1

re3 :: RegExp Int
re3 = Star (Concat ZeroRE (Lit 3)) 

re4 :: RegExp Int
re4 = Concat (Alt (Lit 0) (Lit 1)) (Star (Lit 2))

------------------------------------------------------------------
------------------------------------------------------------------
-- IMPORTANT: Please do not change anything above here.
--            Write all your code below this line.

-----Section 1
fsa_oddEven :: Automaton Int SegmentCV
fsa_oddEven = ([1,2,3,4], [C,V], [1], [3], [(1, C, 2),
                                            (1, V, 3),

                                            (2, C, 1),
                                            (2, V, 4),

                                            (3, C, 4),
                                            (3, V, 1),

                                            (4, V, 2),
                                            (4, C, 3)])


requireCs :: Int -> Automaton Int SegmentCV
requireCs n =
        -- states
        let states = [1 .. n+1] in
        -- alphabet
        let syms = [C,V] in
        -- intial state
        let i = [1] in
        -- end state
        let f = [n+1] in
        -- want a transition from one state to the next using C
        let ctransitions = map (\state -> (state, C, state+1)) [1 .. n] in
        -- want a loop at every state using V
        let vtransitions = map (\state -> (state, V, state)) [1 .. n+1] in
        (states, syms, i, f, ctransitions ++ vtransitions)


----Please submit your answer to Section 2 in a pdf

----Section 3
unionFSAs::(Eq sy) => EpsAutomaton st1 sy -> EpsAutomaton st2 sy -> EpsAutomaton (Either st1 st2) sy
unionFSAs (states1, syms1, initial1, final1, transitions1) (states2, syms2, initial2, final2, transitions2) = 
        let 
                -- new states in new FSA
                newStates = (map First states1) ++ (map Second states2)
                -- new alphabet for new FSA (nub removes duplicates)
                newSyms = nub (syms1 ++ syms2)
                -- new Intial states for new FSA
                newInitialStates = (map First initial1) ++ (map Second initial2)
                -- new final states for new FSA
                newFinalStates = (map First final1) ++ (map Second final2)
                -- new transitions for new FSA
                newTransitions = (map (\(b, t, e) -> (First b, t, First e)) transitions1) ++ (map (\(b, t, e) -> (Second b, t, Second e)) transitions2) 
        in
                (newStates, newSyms, newInitialStates, newFinalStates, newTransitions)


concatFSAs::(Eq sy) => EpsAutomaton st1 sy -> EpsAutomaton st2 sy -> EpsAutomaton (Either st1 st2) sy
concatFSAs (states1, syms1, initial1, final1, transitions1) (states2, syms2, initial2, final2, transitions2) = 
        let 
                -- new states in new FSA
                newStates = (map First states1) ++ (map Second states2)
                -- new alphabet for new FSA (nub removes duplicates)
                newSyms = nub (syms1 ++ syms2)
                -- new Intial states for new FSA (just inital states from first FSA)
                newInitialStates = (map First initial1)
                -- new final states for new FSA (just final states from second FSA)
                newFinalStates = (map Second final2)
                -- new transitions for new FSA
                newTransitions = (map (\(b, t, e) -> (First b, t, First e)) transitions1) ++ (map (\(b, t, e) -> (Second b, t, Second e)) transitions2) ++ [(First finalState, Nothing, Second initialState) | finalState <- final1, initialState <- initial2]
                -- wa want to connect the final states of the first FSA to the initial states of the second FSA using epsilon transitions

        in
                (newStates, newSyms, newInitialStates, newFinalStates, newTransitions)


starFSA::EpsAutomaton st sy -> EpsAutomaton (Either Int st) sy
starFSA (states, syms, initial, final, transitions) = 
        let 
                -- new start state in new FSA 
                newStart = First 0
                -- new states in new FSA (Including new initial state)
                newStates = newStart : (map Second states)
                -- new alphabet stays the same
                newSyms = syms
                -- new Intial states for new FSA (just the new Start state)
                newInitialStates = [newStart]
                -- new final states for new FSA (including start state)
                newFinalStates = newStart : (map Second final)

                -- new transitions for new FSA

                -- all original transitions
                originalTransitions = (map (\(b, t, e) -> (Second b, t, Second e)) transitions)
                -- connect start state to original initial states using epsilon transitions
                newStartTranistions = (map (\i -> (newStart, Nothing, Second i)) initial)
                -- connect final states to initial states using epsilon transitions
                newFinalToInitialTransitions = [(Second finalState, Nothing, Second initialState) | finalState <- final, initialState <- initial]

                newTransitions = originalTransitions ++ newStartTranistions ++ newFinalToInitialTransitions
        in
                (newStates, newSyms, newInitialStates, newFinalStates, newTransitions)


flatten :: Either Int Int -> Int
-- map left input to even number
flatten (First a) = 2 * a
-- map right input to odd number
flatten (Second b) = 2 * b + 1


mapStates::(a -> b) -> EpsAutomaton a sy -> EpsAutomaton b sy
mapStates function (states, syms, initial, final, transitions) = 
        let
                -- use function on all states
                newStates = map function states
        
                -- use function on all inital states
                newInitialStates = map function initial
        
                --  use functionon all final states
                newFinalStates = map function final
        
                -- use the function on all beginning and ending states of all transtions 
                newTransitions = map (\(begin, symbol, end) -> (function begin, symbol, function end)) transitions
        in
                (newStates, syms, newInitialStates, newFinalStates, newTransitions)


reToFSA::(Eq sy) => RegExp sy -> EpsAutomaton Int sy
reToFSA re = case re of
                ZeroRE -> ([0], [], [0], [], [])
                OneRE -> ([0, 1], [], [0], [1], [(0, Nothing, 1)])
                Lit x -> ([0, 1], [x], [0], [1], [(0, Just x, 1)])
                Concat x y -> mapStates flatten (concatFSAs (reToFSA x) (reToFSA y))
                Alt x y -> mapStates flatten (unionFSAs (reToFSA x) (reToFSA y))
                Star x -> mapStates flatten (starFSA (reToFSA x))








