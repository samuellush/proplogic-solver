-- This program implements backtracking using Haskell's lazy evaluation
-- to solve propositional logic formulas.


-- These datatypes define the abstract syntax for propositional logic.

type Name = String              -- Name of a propositional variable

data Prop = Var   Name          -- Propositional variables
          | Not   Prop          -- Negation
          | Or    Prop Prop     -- Disjunction
          | And   Prop Prop     -- Conjunction
          | Imply Prop Prop     -- Implication
            deriving (Show)

-- (Note: We can look up items in an association list using the builtin
--  function lookup :: Eq a => a -> [(a, b)] -> Maybe b.)

-- A couple example propositions.  You can define others to explore the
--   SAT checker.

-- example1 is both satisfiable and falsifiable
example1 = And (Var "a") (Or (Not (Var "a")) (Var "b"))

-- example2 is a tautology (satisfiable but not falsifiable)
example2 = Or (Var "v") (Not (Var "v"))

-- example3 is both satisfiable and falsifiable
example3 = And (Or (Var "p") (Var "q")) (Not (Var "p"))

-- example4 is falsifiable
example4 = Or (And (Var "p") (Var "q")) (Not (Var "p"))

-- example5 is easily satisfiable

example5 = And (Or (Or (Var "p") (Var "q")) (Or (Var "r") (Var "s")))
               (Or (Or (Var "t") (Var "u")) (Or (Var "v") (Var "w")))

-- These are all of the instances returned by trying to satisfy

--  The function satisfyInstances and falsifyInstances return a list of
--    *all possible* sets of variable assignments that could make the given
--    proposition satisfied (for satisfyInstances) or falsified
--    (for falsifyInstances).
--
--  If there is no possible assignment, they return the empty list.
--
--  Thanks to a combination of laziness and recursion the code is functionally
--    equivalent to backtracking.

type Assignments = [(Name,Bool)]        -- List of variable assignments that
                                        --   have been set during the proof.
                                        --   It's an association list.

noAssignments :: Assignments            -- For clarity, we'll define a
noAssignments = []                      --   constant representing an empty set
                                        --   of variable assignments

type AllInstances = [Assignments]       -- All assignments that would work
                                        --   i.e., a list of association lists

satisfyInstances :: Assignments -> Prop -> AllInstances

satisfyInstances assignments (Var varname) =
    case lookup varname assignments of
        Nothing    -> -- Not found. We can make the formula (consisting of just
                      --   this variable) true by making the variable true.
                      --   So we have one successful instance.
                      let newAssignments = (varname, True) : assignments
                      in  [ newAssignments ]
        Just True  -> -- We already decided this variable should be
                      --   true, so just return the variable assignments we
                      --   already have.
                      --   So we have one successful instance.
                      [assignments]
        Just False -> -- Oops...we already decided this variable must be
                      --   false, so we cannot make the given formula true,
                      --   so there are no sucessful instances
                      []

satisfyInstances assignments (Or p1 p2) =
    -- The list of successes is the union of the lists that satisfy p1
    --   and those that satisfy p2.  Note that laziness means that we'll
    --   never compute the second half of the append if we don't need to!!
    satisfyInstances assignments p1 ++ satisfyInstances assignments p2

satisfyInstances assignments (And p1 p2) =
    -- Find assignments that satisfy p1 and also satisfy p2.  Note that
    --   laziness means that we'll only compute as much of the list as we
    --   need to.
    let p1assigns = satisfyInstances assignments p1
        p2assigns = map (\assigns -> satisfyInstances assigns p2) p1assigns
    in  concat p2assigns

satisfyInstances assignments (Not p) =
    -- There is a way to make (Not p) true iff there is a way to make
    --   p false.
    falsifyInstances assignments p

satisfyInstances assignments (Imply p1 p2) =
    -- Use an equivalence of classical propositional logic
    satisfyInstances assignments (Or (Not p1) p2)

falsifyInstances :: Assignments -> Prop -> AllInstances

falsifyInstances assignments (Var varname) =
    case lookup varname assignments of
        Nothing    -> -- Not found. We can make the formula (consisting of just
                      --   this variable) false by making the variable false.
                      --   So we have one successful instance.
                      let newAssignments = (varname, False) : assignments
                      in  [ newAssignments ]
        Just True  -> -- Oops...we already decided this variable must be true,
                      --   so we cannot make the given formula false.
                      --   So there are no successful instances.
                      []
        Just False -> -- We already decided this variable should be
                      --   false; so we have one successful instances.
                      [assignments]

falsifyInstances assignments (And p1 p2) =
    -- The list of falsifications is the union of the lists that faslify p1
    --   and those that faslify p2.
    falsifyInstances assignments p1 ++ falsifyInstances assignments p2

falsifyInstances assignments (Or p1 p2) =
    -- Find assignments that faslify p1 and also faslify p2
    let p1assigns = falsifyInstances assignments p1
        p2assigns = map (\assigns -> falsifyInstances assigns p2) p1assigns
    in  concat p2assigns

falsifyInstances assignments (Not p) =
    -- There is a way to make (Not p) false iff there is a way to
    --   make p true.
    satisfyInstances assignments p

falsifyInstances assignments (Imply p1 p2) =
    -- Use an equivalence of classical propositional logic
    falsifyInstances assignments (Or (Not p1) p2)


-- Check for satisfiability (returning an assignment of values to variables;
--   just returns the first one that works)
satisfy :: Prop -> Maybe Assignments
satisfy p = case satisfyInstances noAssignments p of
                []         -> Nothing
                answer : _ -> Just answer

-- Check for falsifiability (returning an assignment of values to variables;
--   just returns the first one that works)
falsify :: Prop -> Maybe Assignments
falsify p = case falsifyInstances noAssignments p of
                []         -> Nothing
                answer : _ -> Just answer

-- Check for satisfiability (ignoring variable assignments)
satisfiable :: Prop -> Bool
satisfiable p =
    case satisfyInstances noAssignments p of
        [] -> False
        _  -> True

-- Check for falsifiability (ignoring variable assignments)
falsifiable :: Prop -> Bool
falsifiable p =
    case falsifyInstances noAssignments p of
        [] -> False
        _ -> True

-- A tautology checker
valid :: Prop -> Bool
valid p = not (falsifiable p)
