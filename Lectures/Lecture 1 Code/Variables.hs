module Variables where 
-- A module header: keyword 'module' with the name of the module with the keyword 'where'
-- The module definition is the first thing that goes in your Haskell file. 
-- The name of the module begins with a capital letter; each file contains only one module.

n = 4
k = 8







-- Bad, because 'z * z' is an open expression
--g = z * z

-- Ok, because '\z -> z * z' is a closed expression
g = (\z -> z * z)

-------------------------
data Shape = Rock | Paper | Scissors deriving Show -- "Rock", "Paper", "Scissors" are data constructors.  

f = \y -> case y of {Rock -> 0; Paper -> 5; Scissors -> 2}

-- Again bad, because 'case y of ...' is a closed expression
-- f = case y of {Rock -> 0; Paper -> 5; Scissors -> 2}

data Result = Draw | Win Shape deriving Show

--case r of {Draw -> .. ; Win s -> ... s... }


-- We could, if we wanted to, specify the same 4 result options this way
-- But it would be pretty clunky

-- data Result = Draw | WinforRock | WinforPaper | WinforScissors deriving Show
-- case r of {Draw -> ... ; WinforRock -> ... Rock ... ; WinforPaper -> ... Paper ... ; WinforScissors -> ... Scissors ...}


