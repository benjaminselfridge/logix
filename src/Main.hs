{-# LANGUAGE RankNTypes #-}

module Main where

import Calculus
import Calculi
import Parse

import Data.Char
import Data.List
import Data.List.Split
import Data.Maybe
import System.IO

version = "0.2.0"

-- TODO: separate this out into a Utils.hs file
(!!!) :: [a] -> Int -> Maybe a
infixl 9 !!!
(x:xs) !!! n | n == 0    = Just x
             | n <  0    = Nothing
             | otherwise = xs !!! (n-1)
_ !!! _ = Nothing

readMaybe :: Read a => String -> Maybe a
readMaybe s = case reads s of
                [] -> Nothing
                [(a, _)] -> Just a

data Env = Env { goal     :: Derivation
               , subgoal  :: GoalSpec
               , calculus :: Calculus
               , quitFlag :: Bool
               , pretty   :: Bool
               , unicode  :: Bool
               }

getCurrentGoal :: Env -> Derivation
getCurrentGoal env = case getGoal (subgoal env) (goal env) of
  Nothing -> error $ "current subgoal non-existent: " ++ show (subgoal env)
  Just der -> der

-- TODO: for variable term instantiation, ask for binding of the actual variable, not
-- the schematic one.
-- TODO: add "assume" command, maintaining a list of formulas as assumptions that get
-- prepended to every top-level goal. Ultimately want to be able to abbreviate
-- formulas. 
-- TODO: maybe a manual mode, where the user can input the substitution for a
-- particular rule manually? "use" command might be cool
-- TODO: add history command
-- TODO: "examples" command that spits out examples of how to write formulas
-- TODO: add a unicode option. requires separating all show instances into a separate
-- library. 
-- TODO: print help commands with a fixed width.
-- TODO: after switching subgoals, either directly or by applying a rule or axiom,
-- print all applicable rules.
commands :: [(String, (String, [String], Env -> String -> IO Env))]
commands = [ ("help", ("Print all commands.",
                       [],
                       help))
           , ("top", ("Change top-level goal. If given no argument, " ++
                       " just prints the top-level goal.",
                       ["<goal>"],
                       setGoal))
           , ("rule", ("Apply a rule to the current subgoal. If given no argument," ++
                       " just prints all applicable rules.",
                       ["<ruleid>"],
                       rule))
           , ("axiom", ("Apply an axiom to the current subgoal. If given no argument," ++
                       " just prints all applicable axioms.",
                        ["<axiomid>"],
                        axiom))
           , ("goals", ("List all open subgoals.", 
                        [],
                        listGoals))
           , ("goal", ("Change current subgoal. If given no argument, " ++
                       " just prints the current subgoal.",
                       ["<subgoal id>"],
                       changeSubgoal))
           , ("clear", ("Clear the derivation at a particular subgoal.",
                        ["<subgoal>"],
                        clear))
           , ("check", ("Check that each step in a derivation is valid.",
                        [],
                        check))
           , ("tree", ("Print current proof tree.",
                       [],
                       printProofTree))
           , ("pretty", ("Toggle pretty printing for proof tree.",
                         [],
                         togglePretty))
           , ("unicode", ("Toggle unicode printing.",
                          [],
                          toggleUnicode))
           , ("calc", ("Change current calculus. If given no argument, " ++
                       "just prints the current calculus.",
                       ["<calcName>"],
                       changeCalculus))
           , ("ruleinfo", ("List a particular rule or axiom.",
                           ["<ruleName>"],
                           listRule))
           , ("calcs", ("List all available calculi.",
                        [],
                        listCalculi))
           , ("quit", ("Quit.",
                       [],
                       quit))
           ]

help :: Env -> String -> IO Env
help env _ = do mapM_ showCommand commands
                return env
  where showCommand (name, (desc, args, _)) = do
          putStrLn $ name ++ " " ++ intercalate " " args
          putStrLn $ "  " ++ desc

setGoal :: Env -> String -> IO Env
setGoal env arg =
  if null goalString
  then do putStrLn $ ppSequent (unicode env) $ conclusion (goal env)
          return env
  else case parse (sequent <* end) goalString of
    [] -> do putStrLn $ "Couldn't parse sequent \"" ++ goalString ++ "\"."
             return env
    [(sequent,_)] -> do putStrLn $ "Changing goal to \"" ++ ppSequent (unicode env) sequent ++ "\"."
                        return $ env { goal = Stub sequent,
                                     subgoal = []
                                   }
  where goalString = dropWhile (==' ') arg

listGoals :: Env -> String -> IO Env
listGoals env _ = do
  putStrLn "Current open subgoals:"
  mapM_ printGoal (stubs (goal env))
  return env
  where printGoal ([], sequent) = do
          putStr $ if [] == (subgoal env) then " *" else "  "
          putStrLn $ "top: " ++ ppSequent (unicode env) sequent
        printGoal (spec, sequent) = do
          putStr $ if spec == (subgoal env) then " *" else "  "
          putStr $ ppGoalSpec spec
          putStrLn $ ": " ++ ppSequent (unicode env) sequent

changeSubgoal :: Env -> String -> IO Env
changeSubgoal env arg =
  if null subgoalString
  then do let der = getCurrentGoal env
          putStr $ "Current subgoal: " ++ ppSequent (unicode env) (conclusion der)
          putStrLn $ " [" ++ ppGoalSpec (subgoal env) ++ "]"
          return env
  else case getGoal subgoalSpec (goal env) of
         Nothing  -> do putStrLn $ "Nonexistent subgoal: " ++ subgoalString
                        return env
         Just der -> do
           putStr $ "Current subgoal: " ++ ppSequent (unicode env) (conclusion der)
           putStrLn $ " [" ++ ppGoalSpec subgoalSpec ++ "]"
           return $ env { subgoal = subgoalSpec }
  where subgoalString = dropWhile (== ' ') arg
        subgoalSpec = if subgoalString == "top"
                      then []
                      else case sequence $ map readMaybe (splitOn "." subgoalString) of
                             Just spec -> spec
                             Nothing   -> []

clear :: Env -> String -> IO Env
clear env arg =
  if null subgoalString
  then do putStrLn "Please provide a goal (e.g. 1.2.2)"
          return env
  else case clearSubgoal subgoalSpec (goal env) of
         Nothing -> do putStrLn $ "Nonexistent subgoal: " ++ subgoalString
                       return env
         Just newGoal -> do
           putStr $ "Current subgoal: " ++ ppSequent (unicode env) (conclusion newGoal)
           putStrLn $ " [" ++ ppGoalSpec subgoalSpec ++ "]"
           return $ env { goal = newGoal, subgoal = subgoalSpec }
  where subgoalString = dropWhile (== ' ') arg
        subgoalSpec = if subgoalString == "top"
                      then []
                      else case sequence $ map readMaybe (splitOn "." subgoalString) of
                             Just spec -> spec
                             Nothing   -> []
  
-- TODO: make this prettier
check :: Env -> String -> IO Env
check env _ = do
  -- case checkDerivation (calculus env) (goal env) of
  --   Left d -> do
  --     putStrLn "Error in subderivation: "
  --     putStr $ ppDerivation (goal env)
  --   Right () -> do
  --     putStrLn $ "Valid derivation in " ++ name (calculus env)
  putStrLn "check is not implemented currently."
  return env

getFormBindings :: Bool -> [FormulaPat] -> IO FormulaAssignment
getFormBindings unicode [] = return []
getFormBindings unicode (PredPat p:pats) = do
  putStr $ "Need binding for atom " ++ p ++ ":\n  " ++ p ++ " ::= "
  hFlush stdout
  str <- getLine
  let fs = parse (spaces *> atomFormula <* end) str
  case fs of
    [] -> do putStrLn $ "Couldn't parse. Please enter a single atom identifier."
             getFormBindings unicode (PredPat p:pats)
    [(f,_)] -> do rest <- getFormBindings unicode pats
                  return $ (p, [f]) : rest
    x -> error $ "multiple parses for atom: " ++ ppFormulaList unicode (map fst x)
getFormBindings unicode (FormPat a:pats) = do
  putStr $ "Need binding for variable " ++ a ++ ":\n  " ++ a ++ " ::= "
  hFlush stdout
  str <- getLine
  let fs = parse (spaces *> formula <* end) str
  case fs of
    [] -> do putStrLn $ "Couldn't parse. Please enter a single formula."
             getFormBindings unicode (FormPat a:pats)
    [(f,_)] -> do rest <- getFormBindings unicode pats
                  return $ (a, [f]) : rest
    x -> error $ "multiple parses for atom: " ++ ppFormulaList unicode (map fst x)
getFormBindings unicode (SetPat gamma:pats) = do
  putStr $ "Need binding for formula list " ++ gamma ++ ":\n  " ++ gamma ++ " ::= "
  hFlush stdout
  str <- getLine
  let fs = parse (spaces *> formulaList <* end) str
  case fs of
    [] -> do putStrLn $ "Couldn't parse. Please enter a comma-separated list of formulas."
             getFormBindings unicode (SetPat gamma:pats)
    [(fs,_)] -> do rest <- getFormBindings unicode pats
                   return $ (gamma, fs) : rest
    x -> error $ "multiple parses for atom: " ++ intercalate ", " (map (ppFormulaList unicode) (map fst x))
getFormBindings unicode (pat:_) = error $ "can't bind pattern " ++ ppFormulaPat unicode pat

getTermBindings :: Bool -> [TermPat] -> IO TermAssignment
getTermBindings unicode [] = return []
getTermBindings unicode (VarPat x:pats) = do
  putStr $ "Need binding for variable <" ++ x ++ ">:\n  " ++ x ++ " ::= "
  hFlush stdout
  str <- getLine
  let xs = parse (spaces *> many1 alphaNum <* end) str
  case xs of
    [] -> do putStrLn $ "Couldn't parse. Please enter a single variable identifier (like 'x')."
             getTermBindings unicode (VarPat x:pats)
    [(y,_)] -> do rest <- getTermBindings unicode pats
                  return $ (x, VarTerm y) : rest
    _ -> error $ "multiple parses for variable term: " ++ show x
getTermBindings unicode (TermPat t:pats) = do
  putStr $ "Need binding for term <" ++ t ++ ">:\n  " ++ t ++ " ::= "
  hFlush stdout
  str <- getLine
  let ts = parse (spaces *> term <* end) str
  case ts of
    [] -> do putStrLn $ "Couldn't parse. Please enter a term."
             getTermBindings unicode (TermPat t:pats)
    [(t',_)] -> do rest <- getTermBindings unicode pats
                   return $ (t, t') : rest
    _ -> error $ "multiple parses for variable term: " ++ show t
    
getFirstSubgoal :: Derivation -> GoalSpec
getFirstSubgoal der = case stubs der of
  []          -> []
  ((subgoal, _):_) -> subgoal

getNextSubgoal :: Derivation -> GoalSpec -> GoalSpec
getNextSubgoal der spec = getNextSubgoal' (map fst $ stubs der) where
  getNextSubgoal' [] = getFirstSubgoal der
  getNextSubgoal' (stubSpec:specs) | spec <= stubSpec = stubSpec
                                   | otherwise = getNextSubgoal' specs

rule :: Env -> String -> IO Env
rule env arg =
  if null ruleString
  then do putStrLn "Applicable rules: "
          let rules = applicableRules (calculus env) $ conclusion $ getCurrentGoal env
          mapM_ putStrLn (showRules 1 rules)
          return env
  else do let rules = applicableRules (calculus env) $ conclusion $ getCurrentGoal env
          case rules !!! (ruleNum-1) of
            Nothing -> do putStrLn $ "No rule corresponding to " ++ ruleString
                          return env
            Just (name, formBinding, termBinding) -> do
              -- TODO: fix this. tryRule returns a list of unbound terms as well.
              let (unboundForms, unboundTerms) = tryRule (calculus env) name formBinding termBinding
              extraFormBindings <- getFormBindings (unicode env) unboundForms
              extraTermBindings <- getTermBindings (unicode env) unboundTerms
              -- TODO: get term bindings for unbound terms
              case applyRule (calculus env) name
                                 (extraFormBindings ++ formBinding)
                                 (extraTermBindings ++ termBinding)
                                 (subgoal env)
                                 (goal env) of
                Just newGoal -> do
                  putStrLn $ "Applying " ++ name ++ "."
                  let nextSubgoal = getNextSubgoal newGoal (subgoal env)
                  putStrLn $ "Setting active subgoal to " ++ ppGoalSpec nextSubgoal ++
                    ": " ++ ppSequent (unicode env) (conclusion (fromJust (getGoal nextSubgoal newGoal)))
                  return env { goal = newGoal, subgoal = nextSubgoal }
                Nothing -> do
                  putStrLn "Invalid instantiation."
                  return env
  where ruleString = dropWhile (== ' ') arg
        -- TODO: fix this kludge; we really just need to make ruleNum a maybe, and
        -- handle it above.
        ruleNum = case readMaybe ruleString of
                    Just num -> num
                    Nothing  -> 0
        showRule n (name, formBinding, termBinding) =
          case prems of
            [] ->
              "  " ++ show n ++ ". " ++ name ++ " with no obligations"
            [prem] ->
              "  " ++ show n ++ ". " ++ name ++ " with obligations: " ++
              ppSequentInst (unicode env) formBinding termBinding prem
            _      -> 
              "  " ++ show n ++ ". " ++ name ++ " with obligations:\n     " ++
              intercalate "\n     " (map (ppSequentInst (unicode env) formBinding termBinding) prems)
          where Just (prems, _) = lookup name (rules (calculus env))
        showRules n [] = []
        showRules n (x:xs) = showRule n x : showRules (n+1) xs

axiom :: Env -> String -> IO Env
axiom env arg =
  if null axiomString
  then do putStrLn "Applicable axioms: "
          let axioms = applicableAxioms (calculus env) $ conclusion $ getCurrentGoal env
          mapM_ putStrLn (showAxioms 1 axioms)
          return env
  else do let axioms = applicableAxioms (calculus env) $ conclusion $ getCurrentGoal env
          case axioms !!! (axiomNum-1) of
            Nothing -> do putStrLn $ "No axiom corresponding to " ++ axiomString
                          return env
            Just (name, formBinding, termBinding) -> do
              -- we should never have any unbound variables for an axiom, but we
              -- provide this just for the sake of completeness.
              -- TODO: fix this. tryAxiom returns a list of unbound terms as well.
              let unboundVars = fst $ tryAxiom (calculus env) name formBinding termBinding
              extraBindings <- getFormBindings (unicode env) unboundVars
              putStrLn $ "Applying " ++ name ++ "."
              let Just newGoal = applyAxiom (calculus env) name (subgoal env) (goal env)
              let nextSubgoal = getNextSubgoal newGoal (subgoal env)
              putStrLn $ "Setting active subgoal to " ++ ppGoalSpec nextSubgoal ++
                ": " ++ ppSequent (unicode env) (conclusion (fromJust (getGoal nextSubgoal newGoal)))
              return env { goal = newGoal, subgoal = nextSubgoal }
  where axiomString = dropWhile (== ' ') arg
        axiomNum = case readMaybe axiomString of
                    Just num -> num
                    Nothing  -> 0
        showAxiom n (name, formBinding, termBinding) = "  " ++ show n ++ ". " ++ name ++ " with " ++ ppFormulaAssignment formBinding
        showAxioms n [] = []
        showAxioms n (x:xs) = showAxiom n x : showAxioms (n+1) xs
        ppFormulaAssignment bindings = intercalate ", " (map showBinding bindings)
        showBinding (var, [f]) = var ++ " := " ++ ppFormula (unicode env) f
        showBinding (var, fs)  = var ++ " := [" ++ ppFormulaList (unicode env) fs ++ "]"

printProofTree :: Env -> String -> IO Env
printProofTree env _ =
  case (pretty env) of
    True -> do putStr $ ppDerivationTree (unicode env) (goal env) (subgoal env)
               return env
    _    -> do putStr $ ppDerivation (unicode env) (goal env)
               return env

togglePretty :: Env -> String -> IO Env
togglePretty env _ =
  case (pretty env) of
    True  -> do putStrLn "Disabling pretty printing."
                return env { pretty = False }
    _     -> do putStrLn "Enabling pretty printing."
                return env { pretty = True }

toggleUnicode :: Env -> String -> IO Env
toggleUnicode env _ =
  case (unicode env) of
    True  -> do putStrLn "Disabling unicode."
                return env { unicode = False }
    _     -> do putStrLn "Enabling unicode."
                return env { unicode = True }

changeCalculus :: Env -> String -> IO Env
changeCalculus env arg =
  if null calcName
  then do putStrLn $ ppCalculus (unicode env) $ calculus env
          return env
  else 
    case find (\calc -> name calc == calcName) calculi of
      Nothing   -> do putStrLn $ "No calculus named \"" ++ calcName ++ "\"."
                      return env
      Just calc -> do putStrLn $ "Changing calculus to " ++ calcName ++ "."
                      return $ env { calculus = calc }
  where calcName = dropWhile (==' ') arg

-- TODO: fix spacing for axiom
listRule :: Env -> String -> IO Env
listRule env arg =
  case (lookup ruleStr $ axioms (calculus env), lookup ruleStr $ rules (calculus env)) of
    (Just axiomPat,_) -> do putStrLn (ppSequentPat (unicode env) axiomPat ++ " (" ++ ruleStr ++ ")")
                            return env
    (_,Just rulePat)  -> do putStrLn (ppRulePat (unicode env) "" (ruleStr, rulePat))
                            return env
    _                 -> do putStrLn $ "Couldn't find axiom/rule " ++ ruleStr
                            return env
  where ruleStr = dropWhile (==' ') arg

listCalculi :: Env -> String -> IO Env
listCalculi env _ = do mapM_ (\calc -> putStrLn $ name calc) calculi
                       return env

quit :: Env -> String -> IO Env
quit env _ = do { putStrLn "Bye."; return env {quitFlag = True} }

repl :: Env -> IO ()
repl env = do
  putStr "> "
  hFlush stdout
  s <- getLine
  let (com, arg) = break isSpace (dropWhile (==' ') s)
  case lookup com commands of
    Nothing -> do putStrLn $ "Invalid command: " ++ com
                  repl env
    Just (_, _, f) -> do env' <- f env arg
                         case quitFlag env' of
                           True  -> return ()
                           False -> repl env'

introMessage :: String
introMessage =
  "LogiX (Logic Explorer) v. " ++ version ++ "\n" ++
  "interactive proof assistant for sequent calculi\n" ++ 
  "(c) Ben Selfridge 2017\n\n" ++
  "Type \"help\" for a list of commands.\n"

main :: IO ()
main = do
  putStr introMessage
  repl $ Env { goal = Stub ([] :=> [Implies (Pred "P" []) (Pred "P" [])])
             , subgoal = []
             , calculus = head calculi
             , quitFlag = False
             , pretty = True
             , unicode = True
             }
