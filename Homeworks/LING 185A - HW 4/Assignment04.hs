{-# LANGUAGE FlexibleInstances #-}

module Assignment04 where

import Control.Applicative(liftA, liftA2, liftA3)

import SemiringFSA

data Numb = Z | S Numb deriving Show

distrib_lhs :: (Semiring v) => v -> v -> v -> v
distrib_lhs x y z = x &&& (y ||| z)

------------------------------------------------------------------
------------------------------------------------------------------
-- IMPORTANT: Please do not change anything above here.
--            Write all your code below this line.


-- 1. Semiring-based FSAs

backward :: Semiring v => GenericAutomaton st sy v -> [sy] -> st -> v
backward  m w q =
    let (states, syms, i, f, delta) = m in
    case w of
    [] -> f q
    (x:rest) -> gen_or (map (\q1 -> delta (q,x,q1) &&& backward m rest q1) states)

f :: (Semiring v) => GenericAutomaton st sy v -> [sy] -> v
f m w =
    let (states, syms, i, f, delta) = m in
    gen_or (map (\q -> i q &&& backward m w q) states)


-- 2. Adding the cost semiring

addCost :: Cost -> Cost -> Cost
-- add up two costs
addCost (TheInt x) (TheInt y) = TheInt (x + y)
-- Adding anything to an infinite cost should produce an infinite cost
addCost Inf _ = Inf
addCost _ Inf = Inf

minCost :: Cost -> Cost -> Cost
-- selects small of two costs
minCost (TheInt x) (TheInt y) = TheInt (min x y)
-- infinite cost is larger than any other cost
minCost Inf x = x
minCost y Inf = y

instance Semiring Cost where
    x &&& y = addCost x y
    x ||| y = minCost x y
    gtrue = TheInt 0
    gfalse = Inf


-- 3. Adding the set-of-strings semiring

instance Semiring [[a]] where
    x &&& y = [ u ++ v | u <- x, v <- y]
    -- Duplicates don't matter
    x ||| y = x ++ y
    gtrue = [[]]
    gfalse = []

gfsa34 :: GenericAutomaton Int Char [[Char]]
gfsa34 = makeGFSA [] ([1,2,3], ['C','V'],
                    [(1, [[]])], [(1, [[]])],
                    [((1,'V',1), ["V"]),
                     ((1,'C',2), ["C"]),
                     ((1,'V',3), ["V"]),
                     
                     ((2,'V',1), ["V","VV"]),
                     ((2,'V',3), ["V","VV"]),

                     ((3,'C',1), [[]]) ])

gfsa_flap :: GenericAutomaton Int Char [[Char]]
gfsa_flap = makeGFSA [] ([1,2,3], ['a','n','t'],
                        [(1, [[]])], [(1, [[]]), (2, [[]]), (3, ["t"])],

                        [((1,'n',1), ["n"]), 
                         ((1,'t',1), ["t"]),

                         ((1,'a',2), ["a"]),

                         ((2,'n',1), ["n"]),

                         ((2,'a',2), ["a"]),
                         ((2,'t',3), [[]]),

                         ((3,'a',2), ["ta", "Ta"]),

                         ((3,'n',1), ["tn"]),
                         ((3,'t',1), ["tt"]) ])

-- 4. Just when you thought it couldn’t get any more amazing…

gfsa5_count :: GenericAutomaton Int Char Double
gfsa5_count = makeGFSA 0 ([1,2,3], ['C','V'],
                         [(1, 1.0)], [(1, 1.0)], 
                         [((1,'V',1), 1.0),
                          ((1,'C',2), 1.0),
                          ((1,'V',3), 1.0),
                          ((2,'V',1), 1.0),
                          ((2,'V',3), 1.0),
                          ((3,'C',1), 1.0)])

-- the following question is optional
gfsa5_paths :: GenericAutomaton Int Char [[Int]]
gfsa5_paths = makeGFSA [] ([1,2,3], ['C','V'],
                         [(1, [[]])], [(1, [[1]])], 
                         [((1,'V',1), [[1]]),
                          ((1,'C',2), [[1]]),
                          ((1,'V',3), [[1]]),
                          ((2,'V',1), [[2]]),
                          ((2,'V',3), [[2]]),
                          ((3,'C',1), [[3]])])
