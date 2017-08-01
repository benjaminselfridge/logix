{-|
Module      : Sequent
Description : Package for defining sequent calculi, and for proof checking and
              generation. 
Copyright   : (c) Ben Selfridge, 2017
License     : GPL-3
Maintainer  : benselfridge@gmail.com
Stability   : experimental

This module exports a number of datatypes and functions for dealing with
Gentzen-style  sequent calculi. It was inspired by the book ``Structural Proof
Theory'' by Sara Negri and Jan von Plato.

-}

{-# LANGUAGE RankNTypes #-}

module Calculus
  ( -- * Types
    Term(..)
  , TermPat(..)
  , Formula(..)
  , FormulaPat(..)
  , Sequent(..)
  , SequentPat(..)
  , RulePat(..)
  , FormulaAssignment
  , TermAssignment
  , Calculus(..)
  , showFormulaInst
  , showSequentInst
  , instFormulaPat
  , instSequentPat
  
  -- * Pattern operators

  -- * Pattern matching
  , match
  , matchAll

  -- * Derivations
  , Derivation(..)
  , GoalSpec(..)
  , conclusion
  , stubs
  , getGoal
  , applicableAxioms
  , applicableRules
  , applyAxiom
  , applyRule
  , tryAxiom
  , tryRule
--  , checkDerivation
  
  -- * Pretty printing
  , ppRulePat
  , ppGoalSpec
  , ppDerivation
  , ppDerivationTree
  ) where

import Data.List
import Data.Maybe

--------------------------------------------------------------------------------
-- | Represents a single term in propositional calculus.
data Term = ConstTerm String
          | VarTerm   String
          | AppTerm   String [Term]
  deriving (Eq)

--------------------------------------------------------------------------------
-- | Represents a single formula in propositional calculus.
data Formula = Bottom
             | Pred String [Term]
             | And Formula Formula
             | Or Formula Formula
             | Implies Formula Formula
             | Forall String Formula
             | Exists String Formula
  deriving (Eq)

--------------------------------------------------------------------------------
-- substitutions

termVars :: Term -> [String]
termVars (ConstTerm  _) = []
termVars (VarTerm    v) = [v]
termVars (AppTerm _ ts) = [ v | t <- ts, v <- termVars t ]

freeVars :: Formula -> [String]
freeVars = nub . freeVars' where
  freeVars' Bottom = []
  freeVars' (Pred _ ts)   = [ v | t <- ts, v <- termVars t ]
  freeVars' (And     f g) = freeVars' f ++ freeVars' g
  freeVars' (Or      f g) = freeVars' f ++ freeVars' g
  freeVars' (Implies f g) = freeVars' f ++ freeVars' g
  freeVars' (Forall  x f) = [ v | v <- freeVars' f, v /= x ]
  freeVars' (Exists  x f) = [ v | v <- freeVars' f, v /= x ]

substTerm :: String -> Term -> Term -> Term
substTerm x t (VarTerm    v) | x == v = t
substTerm x t (AppTerm f ts) = AppTerm f $ map (substTerm x t) ts
substTerm _ _ term = term

substFormula :: String -> Term -> Formula -> Formula
substFormula _ _ Bottom = Bottom
substFormula x t (Pred p ts) = Pred p $ map (substTerm x t) ts
substFormula x t (And     f g) = And     (substFormula x t f) (substFormula x t g)
substFormula x t (Or      f g) = Or      (substFormula x t f) (substFormula x t g)
substFormula x t (Implies f g) = Implies (substFormula x t f) (substFormula x t g)
substFormula x t (Forall y f) | x == y    = Forall y f
                              | otherwise = Forall y (substFormula x t f)
substFormula x t (Exists y f) | x == y    = Exists y f
                              | otherwise = Exists y (substFormula x t f)

--------------------------------------------------------------------------------
-- | Represents a sequent in a Gentzen-style derivation. Logically, a sequent of the
-- form
--
-- > [f1, f2, ..., fn] :=> [g1, g2, ..., gm] 
--
-- means the /conjunction/ of the f's implies the /disjunction/ of the g's, so if all of
-- the f's are true, then one of the g's must be true.

data Sequent = [Formula] :=> [Formula]
  deriving (Eq)

--------------------------------------------------------------------------------
-- | A TermPat is a placeholder for a 'Term'.

data TermPat = VarPat  { termPatId :: String }
             -- ^ only match variables
             | TermPat { termPatId :: String }
             -- ^ match any term
  deriving (Eq)

--------------------------------------------------------------------------------
-- | A FormulaPat is a placeholder for a 'Formula' or a list of 'Formula's. We make a
-- distinction between /basic/ patterns and /composite/ patterns. Basic patterns are
-- ones that we use as keys in assignments -- PredPat, SubstPat, NoFreePat, FormPat,
-- and SetPat. The rest are composite, and are not by themselves going to make sense
-- as a key in an assignment.

-- TODO: Add more to the above

data FormulaPat = BottomPat
             | PredPat String
             | AndPat FormulaPat FormulaPat
             | OrPat FormulaPat FormulaPat
             | ImpliesPat FormulaPat FormulaPat
             | ForallPat String FormulaPat
             | ExistsPat String FormulaPat
             | SubstPat String TermPat String
             -- ^ substitute arg1 with arg2 in arg3
             | NoFreePat String FormulaPat
             -- ^ arg2 with no free variables matching arg1
             | FormPat String
             -- ^ an /arbitrary/ formula
             | SetPat String
             -- ^ a /list/ of arbitrary formulas
  deriving (Eq)

--------------------------------------------------------------------------------
-- | Pattern for a sequent.
data SequentPat = [FormulaPat] ::=> [FormulaPat]

-- | Pattern for a rule: a list of premises at the top, and a conclusion at the
-- bottom. 
type RulePat = ([SequentPat], SequentPat)

--------------------------------------------------------------------------------
-- | Map from identifiers to terms.

-- | Map from basic patterns to concrete formulas. 
-- type FormulaAssignment = [(FormulaPat, [Formula])]
type FormulaAssignment = [(String, [Formula])]

-- | Map from variable names to concrete terms.
type TermAssignment = [(String, Term)]

instFormulaPat :: FormulaAssignment -> TermAssignment -> FormulaPat -> Maybe [Formula]
instFormulaPat _            _ BottomPat   = return [Bottom]
instFormulaPat formBindings _ (PredPat p) = lookup p formBindings
instFormulaPat formBindings _ (FormPat a) = lookup a formBindings
instFormulaPat formBindings _ (SetPat g)  = lookup g formBindings
instFormulaPat formBindings termBindings (AndPat s t) = do
  sB <- instFormulaPat formBindings termBindings s
  tB <- instFormulaPat formBindings termBindings t
  return [And a b | a <- sB, b <- tB]
instFormulaPat formBindings termBindings (OrPat s t) = do
  sB <- instFormulaPat formBindings termBindings s
  tB <- instFormulaPat formBindings termBindings t
  return [Or a b | a <- sB, b <- tB]
instFormulaPat formBindings termBindings (ImpliesPat s t) = do
  sB <- instFormulaPat formBindings termBindings s
  tB <- instFormulaPat formBindings termBindings t
  return [Implies a b | a <- sB, b <- tB]
instFormulaPat formBindings termBindings (ForallPat x s) = do
  -- TODO: check that this doesn't blow up if x doesn't map to a variable
  VarTerm y <- lookup x termBindings
  sB <- instFormulaPat formBindings termBindings s
  return [Forall y a | a <- sB]
instFormulaPat formBindings termBindings (ExistsPat x s) = do
  VarTerm y <- lookup x termBindings
  sB <- instFormulaPat formBindings termBindings s
  return [Exists y a | a <- sB]
instFormulaPat formBindings termBindings (SubstPat x t s) = do
  VarTerm y <- lookup x termBindings
  let tId = termPatId t
  tB    <- lookup tId termBindings
  sB    <- lookup s formBindings
  return [ substFormula y tB a | a <- sB]
instFormulaPat formBindings termBindings (NoFreePat x s) = do
  VarTerm y <- lookup x termBindings
  sB    <- instFormulaPat formBindings termBindings s
  case y `elem` concat (map freeVars sB) of
    True -> Nothing
    False -> return sB
--  return [ a | a <- sB, not (y `elem` freeVars a) ]

instSequentPat :: FormulaAssignment -> TermAssignment -> SequentPat -> Maybe Sequent
instSequentPat formBindings termBindings (ants ::=> sucs) = do
  antsInsts <- sequence (map (instFormulaPat formBindings termBindings) ants)
  sucsInsts <- sequence (map (instFormulaPat formBindings termBindings) sucs)
  return $ concat antsInsts :=> concat sucsInsts

-- given an assignment and a formula pattern, return a list of all the patterns in
-- the formula that are unbound.
tryFormula :: FormulaAssignment -> TermAssignment -> FormulaPat -> ([FormulaPat], [TermPat])
tryFormula _ _ BottomPat = ([], [])
tryFormula formBindings termBindings (PredPat p) =
  case lookup p formBindings of
    Nothing -> ([PredPat p], [])
    Just _  -> ([], [])
tryFormula formBindings termBindings (FormPat p) =
  case lookup p formBindings of
    Nothing -> ([FormPat p], [])
    Just _  -> ([], [])
tryFormula formBindings termBindings (SetPat p) =
  case lookup p formBindings of
    Nothing -> ([SetPat p], [])
    Just _  -> ([], [])
tryFormula formBindings termBindings (AndPat s t) = (sForms ++ tForms, sTerms ++ tTerms) where
  (sForms, sTerms) = tryFormula formBindings termBindings s
  (tForms, tTerms) = tryFormula formBindings termBindings t
tryFormula formBindings termBindings (OrPat s t) = (sForms ++ tForms, sTerms ++ tTerms) where
  (sForms, sTerms) = tryFormula formBindings termBindings s
  (tForms, tTerms) = tryFormula formBindings termBindings t
tryFormula formBindings termBindings (ImpliesPat s t) = (sForms ++ tForms, sTerms ++ tTerms) where
  (sForms, sTerms) = tryFormula formBindings termBindings s
  (tForms, tTerms) = tryFormula formBindings termBindings t
tryFormula formBindings termBindings (ForallPat x s) = (sForms, xTerms ++ sTerms) where
  (sForms, sTerms) = tryFormula formBindings termBindings s
  xTerms = case lookup x termBindings of
    Nothing -> [VarPat x]
    Just _  -> []
tryFormula formBindings termBindings (ExistsPat x s) = (sForms, xTerms ++ sTerms) where
  (sForms, sTerms) = tryFormula formBindings termBindings s
  xTerms = case lookup x termBindings of
    Nothing -> [VarPat x]
    Just _  -> []
tryFormula formBindings termBindings (SubstPat x t s) = (sForms, xTerms ++ tTerms) where
  sForms = case lookup s formBindings of
    Nothing -> [FormPat s]
    Just _  -> []
  xTerms = case lookup x termBindings of
    Nothing -> [VarPat x]
    Just _  -> []
  tTerms = case lookup (termPatId t) termBindings of
    Nothing -> [t]
    Just _  -> []
tryFormula formBindings termBindings (NoFreePat x s) = (sForms, xTerms ++ sTerms) where
  (sForms, sTerms) = tryFormula formBindings termBindings s
  xTerms = case lookup x termBindings of
    Nothing -> [VarPat x]
    Just _ -> []

appendPair :: ([a],[b]) -> ([a],[b]) -> ([a],[b])
appendPair (xs, ys) (xs', ys') = (xs ++ xs', ys ++ ys')

concatPairs :: [([a],[b])] -> ([a],[b])
concatPairs = foldl appendPair ([],[])

nubPair :: (Eq a, Eq b) => ([a],[b]) -> ([a],[b])
nubPair (xs, ys) = (nub xs, nub ys)

-- TODO: removed a nub from the front of below, should be safe since there is a nub
-- in front of all uses of this function anyway.
trySequent :: FormulaAssignment -> TermAssignment -> SequentPat -> ([FormulaPat], [TermPat])
trySequent formBindings termBindings (ants ::=> sucs) =
  tryFormulas' formBindings termBindings ants `appendPair` tryFormulas' formBindings termBindings sucs
  where tryFormulas' formBindings termBindings pats = concatPairs $ map (tryFormula formBindings termBindings) pats

--------------------------------------------------------------------------------
-- Matching patterns

-- (i-am-here)

-- | powerset of a list, viewed as a multiset.
powerset :: [a] -> [[a]]
powerset (x:xs) = [ x : px | px <- pxs ] ++ pxs
  where pxs = powerset xs
powerset [] = [[]]

-- | merge two assignments if they are in agreement; otherwise return Nothing
mergeFormulaAssignments :: [FormulaAssignment] -> [FormulaAssignment]
mergeFormulaAssignments (((n, cs):a1):assigns) = do
  mergeRest <- mergeFormulaAssignments (a1:assigns)
  case lookup n mergeRest of
    Nothing -> return $ (n, cs) : mergeRest
    Just cs' | cs == cs' -> return mergeRest
    _ -> []
mergeFormulaAssignments ([]:assigns) = mergeFormulaAssignments assigns
mergeFormulaAssignments [] = return []

mergeTermAssignments :: [TermAssignment] -> [TermAssignment]
mergeTermAssignments (((n, cs):a1):assigns) = do
  mergeRest <- mergeTermAssignments (a1:assigns)
  case lookup n mergeRest of
    Nothing -> return $ (n, cs) : mergeRest
    Just cs' | cs == cs' -> return mergeRest
    _ -> []
mergeTermAssignments ([]:assigns) = mergeTermAssignments assigns
mergeTermAssignments [] = return []
  
-- | Take a list of patterns and a list of formulas to match, and produce a list
-- of all satisfying assignments.
match :: [FormulaPat] -> [Formula] -> [(FormulaAssignment,TermAssignment)]
--match :: [FormulaPat] -> [Formula] -> [FormulaAssignment]
match (BottomPat:pats) fs =
  [matchRest | Bottom    <- nub fs
             , fs'       <- [delete Bottom fs]
             , matchRest <- match pats fs']
-- match ((PredPat p):pats) fs =
--   [merge | Pred p' ts <- nub fs
--          , matchForms <- match pats (delete (Pred p' ts) fs)
--          , merge <- mergeFormulaAssignments [[(p, [Pred p' ts])], matchForms]]
match ((PredPat p):pats) fs =
  [(merge, matchTerms) | Pred p' ts <- nub fs
                       , (matchForms, matchTerms) <- match pats (delete (Pred p' ts) fs)
                       , merge <- mergeFormulaAssignments [[(p, [Pred p' ts])], matchForms]]
-- match ((FormPat n):pats) fs =
--   [merge | y          <- nub fs
--          , assignRest <- match pats (delete y fs)
--          , merge      <- mergeFormulaAssignments [[(n,[y])], assignRest]]
match ((FormPat n):pats) fs =
  [(mergeForms, matchTerms) | y <- nub fs
                            , (matchForms, matchTerms) <- match pats (delete y fs)
                            , mergeForms <- mergeFormulaAssignments [[(n,[y])], matchForms]]
-- match ((AndPat pat1 pat2):pats) fs =
--   [merge | And c1 c2  <- nub fs
--          , matchc1    <- match [pat1] [c1]
--          , matchc2    <- match [pat2] [c2]
--          , assignRest <- match pats (delete (And c1 c2) fs)
--          , merge      <- mergeFormulaAssignments [matchc1, matchc2, assignRest]]
match ((AndPat pat1 pat2):pats) fs =
  [(mergeForms, matchTerms) | And c1 c2 <- nub fs
                            , (c1Forms, c1Terms) <- match [pat1] [c1]
                            , (c2Forms, c2Terms) <- match [pat2] [c2]
                            , (matchForms, matchTerms) <- match pats (delete (And c1 c2) fs)
                            , mergeForms <- mergeFormulaAssignments [c1Forms, c2Forms, matchForms]
                            , mergeTerms <- mergeTermAssignments [c1Terms, c2Terms, matchTerms]]
match ((OrPat pat1 pat2):pats) fs =
  [(mergeForms, matchTerms) | Or c1 c2 <- nub fs
                            , (c1Forms, c1Terms) <- match [pat1] [c1]
                            , (c2Forms, c2Terms) <- match [pat2] [c2]
                            , (matchForms, matchTerms) <- match pats (delete (Or c1 c2) fs)
                            , mergeForms <- mergeFormulaAssignments [c1Forms, c2Forms, matchForms]
                            , mergeTerms <- mergeTermAssignments [c1Terms, c2Terms, matchTerms]]
match ((ImpliesPat pat1 pat2):pats) fs =
  [(mergeForms, matchTerms) | Implies c1 c2 <- nub fs
                            , (c1Forms, c1Terms) <- match [pat1] [c1]
                            , (c2Forms, c2Terms) <- match [pat2] [c2]
                            , (matchForms, matchTerms) <- match pats (delete (Implies c1 c2) fs)
                            , mergeForms <- mergeFormulaAssignments [c1Forms, c2Forms, matchForms]
                            , mergeTerms <- mergeTermAssignments [c1Terms, c2Terms, matchTerms]]
-- match ((SetPat s):pats) fs =
--   [merge | fs'        <- nub $ powerset fs
--          , assignRest <- match pats (fs \\ fs')
--          , merge      <- mergeFormulaAssignments [[(s,fs')], assignRest]]
match ((SetPat s):pats) fs =
  [(mergeForms, matchTerms) | fs' <- nub $ powerset fs
                            , (matchForms, matchTerms) <- match pats (fs \\ fs')
                            , mergeForms <- mergeFormulaAssignments [[(s,fs')], matchForms]]
match ((ForallPat x pat):pats) fs =
  [(mergeForms, mergeTerms) | Forall y f <- nub fs
                            , (fForms, fTerms) <- match [pat] [f]
                            , (matchForms, matchTerms) <- match pats (delete (Forall y f) fs)
                            , mergeForms <- mergeFormulaAssignments [fForms, matchForms]
                            , mergeTerms <- mergeTermAssignments [[(x, VarTerm y)], fTerms, matchTerms]]
match ((ExistsPat x pat):pats) fs =
  [(mergeForms, mergeTerms) | Exists y f <- nub fs
                            , (fForms, fTerms) <- match [pat] [f]
                            , (matchForms, matchTerms) <- match pats (delete (Exists y f) fs)
                            , mergeForms <- mergeFormulaAssignments [fForms, matchForms]
                            , mergeTerms <- mergeTermAssignments [[(x, VarTerm y)], fTerms, matchTerms]]
match ((SubstPat x t n):pats) fs =
  [(mergeForms, matchTerms) | y <- nub fs
                            , (matchForms, matchTerms) <- match pats (delete y fs)
                            , mergeForms <- mergeFormulaAssignments [[(n,[y])], matchForms]]
match ((NoFreePat x pat):pats) fs =
  -- We can't check the no free part here because we don't yet know what actual
  -- variable the metavariable x is going to be assigned to.
  [(mergeForms, mergeTerms) | fs' <- nub $ powerset fs
                            , (patForms, patTerms) <- match [pat] fs'
                            , (matchForms, matchTerms) <- match pats (fs \\ fs')
                            , mergeForms <- mergeFormulaAssignments [patForms, matchForms]
                            , mergeTerms <- mergeTermAssignments [patTerms, matchTerms]]
match [] [] = [([],[])]
match [] _ = []

oneOfEach :: [[a]] -> [[a]]
oneOfEach ((x:xs):rst) = [ x : l | l <- oneOfEach rst ] ++ oneOfEach (xs:rst)
oneOfEach ([]:rst) = []
oneOfEach [] = [[]]

-- | Given a list of constraints, produce all assignments that satisfy every
-- constraint.
matchAll :: [([FormulaPat], [Formula])] -> [(FormulaAssignment,TermAssignment)]
matchAll pairs = do
  let matchPairs = map (uncurry match) pairs
  bindings <- oneOfEach matchPairs
  let formBindings = map fst bindings
  let termBindings = map snd bindings
  mergeForms <- mergeFormulaAssignments formBindings
  mergeTerms <- mergeTermAssignments termBindings
  return (mergeForms, mergeTerms)

--------------------------------------------------------------------------------
-- | Gentzen-style calculus, defined using patterns. Example use:
--
-- @
--
-- atom = AtomPat \"P\"
-- a = FormPat \"A\"
-- b = FormPat \"B\"
-- c = FormPat \"C\"
-- gamma = SetPat \"Gamma\"
--
-- g3ip :: Calculus
-- g3ip = Calculus {
--   name = \"G3ip\",
--   axioms = [(\"Axiom\", [atom, gamma] ::=> [atom])],
--   rules = 
--   [ (\"R&\",   ([ [gamma] ::=> [a],
--                 [gamma] ::=> [b] ]
--               , [gamma] ::=> [a $& b]))
--
--   , (\"R|1\",  ([ [gamma] ::=> [a] ]
--               , [gamma] ::=> [a $| b]))
--
--   , (\"R|2\",  ([ [gamma] ::=> [b] ]
--               , [gamma] ::=> [a $| b]))
--
--   , (\"R->\",  ([ [a, gamma] ::=> [b] ]
--               , [gamma] ::=> [a $> b]))
--
--   , (\"L&\",   ([ [a, b, gamma] ::=> [c] ]
--               , [a $& b, gamma] ::=> [c]))
--
--   , (\"L|\",   ([ [a, gamma] ::=> [c], [b, gamma] ::=> [c] ]
--               , [a $| b, gamma] ::=> [c]))
--
--   , (\"L->\",  ([ [a $> b, gamma] ::=> [a], [b, gamma] ::=> [c] ]
--               , [a $> b, gamma] ::=> [c]))
--
--   , (\"L_|_\", ([ ]
--               , [botpat, gamma] ::=> [c]))
--   ]}
-- @
data Calculus = Calculus { name :: String
                         , axioms :: [(String, SequentPat)]
                         , rules :: [(String, RulePat)]
                         }

--------------------------------------------------------------------------------
-- | Partial derivation.

data Derivation = Stub  Sequent
                | Axiom Sequent String
                | Der   Sequent String [Derivation]

-- | Return all applicable axioms for a sequent. Gives the name of the axiom, and
-- the assignment that will match the formula to the conclusion of the axiom.
applicableAxioms :: Calculus -> Sequent -> [(String, FormulaAssignment, TermAssignment)]
applicableAxioms calculus (ants :=> sucs) = do
  (name, antPats ::=> sucPats) <- axioms calculus
  (formBinding, termBinding) <- matchAll [(antPats, ants), (sucPats, sucs)]
  return (name, formBinding, termBinding)

-- | Return all applicable rules for a sequent. Gives the name of the rule, and
-- the assignment that will match the formula to the conclusion of the rule.
applicableRules :: Calculus -> Sequent -> [(String, FormulaAssignment, TermAssignment)]
applicableRules calculus (ants :=> sucs) = do
  (name, (_, antPats ::=> sucPats)) <- rules calculus
  (formBinding, termBinding) <- matchAll [(antPats, ants), (sucPats, sucs)]
  return (name, formBinding, termBinding)

-- | A pointer into a derivation, representing a subgoal. Empty list represents the
-- root of the derivation; [1,2] means look at the first subderivation, then the
-- second subderivation of that, etc.
type GoalSpec = [Int]

-- | Get all the 'Stub's in a derivation. Returns a list of pairs, where we get both
-- the 'GoalSpec' (i.e. the path to the 'Stub') and the sequent of the 'Stub'.
stubs :: Derivation -> [(GoalSpec, Sequent)]
stubs (Stub sequent) = [([], sequent)]
stubs (Axiom _ _)    = []
stubs (Der _ _ ders) = concat $ numberAll 1 $ map stubs ders
  where 
    number n (goalSpec, sequent) = (n:goalSpec, sequent)
    numberAll n [] = []
    numberAll n (x:xs) = map (number n) x : numberAll (n+1) xs

(!!!) :: [a] -> Int -> Maybe a
infixl 9 !!!
(x:xs) !!! n | n == 0    = Just x
             | n <  0    = Nothing
             | otherwise = xs !!! (n-1)
_ !!! _ = Nothing

-- | Given a 'GoalSpec' and a 'Derivation', traverse the derivation tree and find the sub-derivation
-- pointed to by that 'GoalSpec'.
getGoal :: GoalSpec -> Derivation -> Maybe Derivation
getGoal [] der = Just der
getGoal (x:xs) (Der _ _ ders) = do
  der <- ders !!! (x-1)
  getGoal xs der
getGoal _ _ = Nothing

-- | Get the conclusion of a derivation (the sequent that appears underneath the line).
conclusion :: Derivation -> Sequent
conclusion (Stub  sequent)     = sequent
conclusion (Axiom sequent _)   = sequent
conclusion (Der   sequent _ _) = sequent

setElt :: Int -> a -> [a] -> [a]
setElt _ _ [] = []
setElt 0 x (y:ys) = x : ys
setElt n x (y:ys) | n > 0 = y : (setElt (n-1) x ys)

-- | Given a 'Calculus', a axiom name, a 'GoalSpec' (pointer to a particular node in
-- the derivation tree), and a 'Derivation', return a new derivation consisting of
-- the old one with the given node replaced with an axiom application. Fails if the
-- node doesn't exist.
applyAxiom :: Calculus -> String -> GoalSpec -> Derivation -> Maybe Derivation
applyAxiom calculus name [] (Stub sequent) = Just $ Axiom sequent name
applyAxiom calculus name (x:xs) (Der sequent rule ders) = do
  der <- ders !!! (x-1)
  newDer <- applyAxiom calculus name xs der
  return $ Der sequent rule (setElt (x-1) newDer ders)

-- | Given a calculus, an axiom of that calculus, and an assignment, return a list of
-- all the unbound variables in the axiom.
tryAxiom :: Calculus -> String -> FormulaAssignment -> TermAssignment -> ([FormulaPat],[TermPat])
tryAxiom calculus name formBindings termBindings = case pat of
  Nothing -> ([],[])
  Just sequent -> trySequent formBindings termBindings sequent
  where pat = lookup name (axioms calculus)

-- | Given a 'Calculus', a rule name, an assignment for the rule, a 'GoalSpec'
-- (pointer to a particular node in the derivation tree), and a 'Derivation', return
-- a new derivation consisting of the old one with the given node replaced with a
-- rule application. Fails if the node doesn't exist.
applyRule :: Calculus -> String -> FormulaAssignment -> TermAssignment -> GoalSpec -> Derivation -> Maybe Derivation
applyRule calculus name formBindings termBindings [] der = do
  (prems, conc) <- lookup name (rules calculus)
  premInsts <- sequence $ map (instSequentPat formBindings termBindings) prems
  concInst <- instSequentPat formBindings termBindings conc
  return $ Der (conclusion der) name (map Stub premInsts)
applyRule calculus name formBindings termBindings (x:xs) (Der sequent rule ders) = do
  der <- ders !!! (x-1)
  newDer <- applyRule calculus name formBindings termBindings xs der
  return $ Der sequent rule (setElt (x-1) newDer ders)

-- | Given a calculus, a rule of that calculus, and an assignment, return a list of
-- all the unbound variables in the rule.
tryRule :: Calculus -> String -> FormulaAssignment -> TermAssignment -> ([FormulaPat],[TermPat])
tryRule calculus name formBindings termBindings = case pat of
  Nothing -> ([],[])
  Just (prems, conc) ->
    nubPair $ trySequent formBindings termBindings conc `appendPair` concatPairs (map (trySequent formBindings termBindings) prems)
  where pat = lookup name (rules calculus)

-- TODO: fix this
-- | Given a "Calculus" and a "Derivation", check that the derivation is valid.
-- checkDerivation :: Calculus -> Derivation -> Either Derivation ()
-- checkDerivation calculus (Stub _) = return ()
-- checkDerivation calculus d@(Axiom conc axiom)
--   | Just (lax ::=> rax) <- lookup axiom (axioms calculus)
--   , (l :=> r) <- conc = do
--       let matches = matchAll [(lax, l), (rax, r)]
--       case matches of
--         [] -> Left d
--         _  -> return ()
-- checkDerivation calculus d@(Der conc rule prems)
--   | Just (rulePrems, ruleConc) <- lookup rule (rules calculus)
--   , formulas <- foldl (++) [] (map (\(l  :=> r) -> [l,r]) (conc:map conclusion prems))
--   , patterns <- foldl (++) [] (map (\(l ::=> r) -> [l,r]) (ruleConc:rulePrems)) = do
--       mapM_ (checkDerivation calculus) prems
--       let matches = matchAll (zipAll patterns formulas)
--           -- use zipAll to make sure we 
--       case matches of
--         [] -> Left d
--         _ -> return ()
--   where zipAll (a:as) (b:bs) = (a,b)  : zipAll as bs
--         zipAll (a:as) []     = (a,[]) : zipAll as []
--         zipAll []     (b:bs) = ([],b) : zipAll [] bs
--         zipAll []     []     = []
-- checkDerivation _ d = Left d -- rule not found

--------------------------------------------------------------------------------
-- show instances

instance Show Term where
  show (ConstTerm  c) = "_" ++ c
  show (VarTerm    v) = v
  show (AppTerm f ts) = f ++ "(" ++ intercalate ", " (map show ts) ++ ")"

-- TODO: clean all this shit up somehow

showFormula' Bottom        = "_|_"
showFormula' (Pred p [])   = p
showFormula' (Pred p ts)   = p ++ "(" ++ intercalate ", " (map show ts) ++ ")"
showFormula' (And (Implies a b) (Implies b' a'))
  | a == a', b == b'       = "(" ++ showFormula' a ++ " <-> " ++ showFormula' b ++ ")"
showFormula' (And a b)     = "(" ++ showFormula' a ++ " & "   ++ showFormula' b ++ ")"
showFormula' (Or a b)      = "(" ++ showFormula' a ++ " | "   ++ showFormula' b ++ ")"
showFormula' (Implies a Bottom)
                           = "~" ++ showFormula' a
showFormula' (Implies a b) = "(" ++ showFormula' a ++ " -> "  ++ showFormula' b ++ ")"
showFormula' (Forall x a) = "∀" ++ x ++ showFormula' a
showFormula' (Exists x a) = "∃" ++ x ++ showFormula' a

showFormula (And (Implies a b) (Implies b' a'))
  | a == a', b == b'     = showFormula' a ++ " <-> " ++ showFormula' b
showFormula (And a b)          = showFormula' a ++ " & " ++ showFormula' b
showFormula (Or a b)           = showFormula' a ++ " | " ++ showFormula' b
showFormula (Implies a Bottom) = "~" ++ showFormula' a
showFormula (Implies a b)      = showFormula' a ++ " -> " ++ showFormula' b
showFormula formula            = showFormula' formula

instance Show Formula where
  show = showFormula

instance Show Sequent where
  show (ants :=> sucs) = intercalate ", " (map show ants) ++ " => " ++
                         intercalate ", " (map show sucs)

-- TODO: g3i, top => ~exists x.P(x) -> forall x.~P(x) leads to a presentation of ~ as
-- -> _|_.
showFormulaPat' (PredPat p) = p
showFormulaPat' (FormPat a) = a
showFormulaPat' (SetPat gamma) = gamma
showFormulaPat' (AndPat (ImpliesPat s t) (ImpliesPat t' s'))
  | s == s' && t == t' = "(" ++ showFormulaPat' s ++ " <-> " ++ showFormulaPat' t ++ ")"
showFormulaPat' (AndPat     s t) = "(" ++ showFormulaPat' s ++ " & "  ++ showFormulaPat' t ++ ")"
showFormulaPat' (OrPat      s t) = "(" ++ showFormulaPat' s ++ " | "  ++ showFormulaPat' t ++ ")"
showFormulaPat' (ImpliesPat s BottomPat) = "~" ++ showFormulaPat' s
showFormulaPat' (ImpliesPat s t) = "(" ++ showFormulaPat' s ++ " -> " ++ showFormulaPat' t ++ ")"
showFormulaPat' (ForallPat x s) = "∀" ++ x ++ "(" ++ showFormulaPat' s ++ ")"
showFormulaPat' (ExistsPat x s) = "∃" ++ x ++ "(" ++ showFormulaPat' s ++ ")"
showFormulaPat' (SubstPat x t a) = a ++ "(" ++ termPatId t ++ "/" ++ x ++ ")"
showFormulaPat' (NoFreePat x s) = showFormulaPat' s ++ "[no free " ++ x ++ "]"
showFormulaPat' (BottomPat) = "_|_"

showFormulaPat (AndPat (ImpliesPat s t) (ImpliesPat t' s'))
  | s == s' && t == t' = showFormulaPat' s ++ " <-> " ++ showFormulaPat' t
showFormulaPat (AndPat     s t) = showFormulaPat' s ++ " & "  ++ showFormulaPat' t
showFormulaPat (OrPat      s t) = showFormulaPat' s ++ " | "  ++ showFormulaPat' t
showFormulaPat (ImpliesPat s BottomPat) = "~" ++ showFormulaPat' s
showFormulaPat (ImpliesPat s t) = showFormulaPat' s ++ " -> " ++ showFormulaPat' t
showFormulaPat f = showFormulaPat' f

instance Show FormulaPat where
  show = showFormulaPat

showFormulaInst' :: FormulaAssignment -> TermAssignment -> FormulaPat -> String
showFormulaInst' formBindings termBindings (PredPat p) = case lookup p formBindings of
  Nothing  -> "[[" ++ p ++ "]]" -- p is unbound
  Just [f] -> showFormula' f
  Just fs  -> error $ "atom variable " ++ p ++ " bound to " ++ show fs
showFormulaInst' formBindings termBindings (FormPat a) = case lookup a formBindings of
  Nothing  -> "[[" ++ a ++ "]]"
  Just [f] -> showFormula' f
  -- use showFormula' instead of show to ensure it gets parenthesized
  Just fs  -> error $ "var variable " ++ a ++ " bound to " ++ show fs
showFormulaInst' formBindings termBindings (SetPat g) = case lookup g formBindings of
  Nothing -> "[[" ++ g ++ "]]"
  Just fs -> intercalate ", " (map show fs) -- show the formulas
showFormulaInst' formBindings termBindings (AndPat (ImpliesPat s t) (ImpliesPat t' s'))
  | s == s' && t == t' =
    "(" ++ showFormulaInst' formBindings termBindings s ++ " <-> " ++ showFormulaInst' formBindings termBindings t ++ ")"
showFormulaInst' formBindings termBindings (AndPat s t) =
  "(" ++ showFormulaInst' formBindings termBindings s ++ " & " ++ showFormulaInst' formBindings termBindings t ++ ")"
showFormulaInst' formBindings termBindings (OrPat s t) =
  "(" ++ showFormulaInst' formBindings termBindings s ++ " | " ++ showFormulaInst' formBindings termBindings t ++ ")"
showFormulaInst' formBindings termBindings (ImpliesPat s BottomPat) = "~" ++ showFormulaInst' formBindings termBindings s
showFormulaInst' formBindings termBindings (ImpliesPat s t) =
  "(" ++ showFormulaInst' formBindings termBindings s ++ " -> " ++ showFormulaInst' formBindings termBindings t ++ ")"
showFormulaInst' formBindings termBindings BottomPat = "_|_"
showFormulaInst' formBindings termBindings (ForallPat x s) =
  case lookup x termBindings of
    Nothing -> "∀[[" ++  x ++ "]]." ++ showFormulaInst' formBindings termBindings s
    Just (VarTerm y) -> "∀" ++ y ++ "." ++ showFormulaInst' formBindings termBindings s
showFormulaInst' formBindings termBindings (ExistsPat x s) =
  case lookup x termBindings of
    Nothing -> "∃[[" ++  x ++ "]]." ++ showFormulaInst' formBindings termBindings s
    Just (VarTerm y) -> "∃" ++ y ++ "." ++ showFormulaInst' formBindings termBindings s
showFormulaInst' formBindings termBindings (SubstPat x t s) =
  let xStr = case lookup x termBindings of
               Nothing -> "[[" ++ x ++ "]]"
               Just (VarTerm y) -> y
      tStr = case lookup (termPatId t) termBindings of
               Nothing -> "[[" ++ termPatId t ++ "]]"
               Just t' -> show t'
      sStr = case lookup s formBindings of
               Nothing -> "[[" ++ s ++ "]]"
               Just s' -> show s'
  in sStr ++ "(" ++ tStr ++ "/" ++ xStr ++ ")"
showFormulaInst' formBindings termBindings (NoFreePat x s) =
  case lookup x termBindings of
    Nothing -> showFormulaInst' formBindings termBindings s ++ "[no free [[" ++ x ++ "]] ]"
    Just (VarTerm y) -> showFormulaInst' formBindings termBindings s ++ "[no free " ++ y ++ "]"
  
-- | Given a (possibly incomplete) assignment and a formula pattern, pretty print the
-- instantiation. 
showFormulaInst :: FormulaAssignment -> TermAssignment -> FormulaPat -> String
showFormulaInst formBindings termBindings (FormPat a) = case lookup a formBindings of
  Nothing -> "[[" ++ a ++ "]]"
  Just [f] -> show f
  Just fs -> error $ "var variable " ++ a ++ " bound to " ++ show fs
showFormulaInst formBindings termBindings (AndPat (ImpliesPat s t) (ImpliesPat t' s'))
  | s == s' && t == t' =
    showFormulaInst' formBindings termBindings s ++ " <-> " ++ showFormulaInst' formBindings termBindings t
showFormulaInst formBindings termBindings (AndPat s t) =
  showFormulaInst' formBindings termBindings s ++ " & " ++ showFormulaInst' formBindings termBindings t
showFormulaInst formBindings termBindings (OrPat s t) =
  showFormulaInst' formBindings termBindings s ++ " | " ++ showFormulaInst' formBindings termBindings t
showFormulaInst formBindings termBindings (ImpliesPat s BottomPat) = "~" ++ showFormulaInst' formBindings termBindings s
showFormulaInst formBindings termBindings (ImpliesPat s t) =
  showFormulaInst' formBindings termBindings s ++ " -> " ++ showFormulaInst' formBindings termBindings t
showFormulaInst formBindings termBindings pat = showFormulaInst' formBindings termBindings pat

showSequentPat' (ants ::=> sucs) = intercalate ", " (map show ants) ++ " => " ++
                                   intercalate ", " (map show sucs)

instance Show SequentPat where
  show = showSequentPat'

-- | Given a (possibly incomplete) assignment and a sequent pattern, pretty print the
-- instantiation.
showSequentInst :: FormulaAssignment -> TermAssignment -> SequentPat -> String
showSequentInst formBindings termBindings (ants ::=> sucs) =
  intercalate ", " (filter (not . null) (map (showFormulaInst formBindings termBindings) ants)) ++
   " => " ++
  intercalate ", " (filter (not . null) (map (showFormulaInst formBindings termBindings) sucs))

-- | Pretty print a rule pattern.
ppRulePat :: String -> (String, RulePat) -> String
ppRulePat pad (name, (premises, conclusion)) =
  let pStr = intercalate "   " (map show premises)
      pWidth = length pStr
      cStr = show conclusion
      cWidth = length cStr
      totalWidth = max pWidth cWidth
      pPad = (totalWidth - pWidth) `div` 2
      cPad = (totalWidth - cWidth) `div` 2
  in pad ++ replicate pPad ' ' ++ pStr ++ "\n" ++
     pad ++ replicate totalWidth '-' ++ " (" ++ name ++ ")\n" ++
     pad ++ replicate cPad ' ' ++ cStr

atoms :: FormulaPat -> [String]
atoms (PredPat p) = [p]
atoms (AndPat s t) = atoms s ++ atoms t
atoms (OrPat s t) = atoms s ++ atoms t
atoms (ImpliesPat s t) = atoms s ++ atoms t
atoms _ = []

formulas :: FormulaPat -> [String]
formulas (FormPat a) = [a]
formulas (AndPat s t) = formulas s ++ formulas t
formulas (OrPat s t) = formulas s ++ formulas t
formulas (ImpliesPat s t) = formulas s ++ formulas t
formulas _ = []

contexts :: FormulaPat -> [String]
contexts (SetPat a) = [a]
contexts (AndPat s t) = contexts s ++ contexts t
contexts (OrPat s t) = contexts s ++ contexts t
contexts (ImpliesPat s t) = contexts s ++ contexts t
contexts _ = []

-- TODO: add variables and terms to the "where" clause
ppCalculus :: Calculus -> String
ppCalculus (Calculus name axioms rules) =
  "Calculus " ++ name ++ ".\n\n" ++
  "Axioms:\n" ++ concat (map showAxiom axioms) ++ "\n" ++
  "Rules:\n\n" ++ concat (map showRule rules) ++
  qualString

  where showAxiom (axiomName, axiomPattern) =
          "  " ++ show axiomPattern ++ " (" ++ axiomName ++ ")\n"
        showRule rule = ppRulePat "  " rule ++ "\n\n"

        patternAtoms (ants ::=> sucs) = concat $ map atoms ants ++ map atoms sucs
        axiomAtoms = concat $ map patternAtoms (map snd axioms)
        rulePatternAtoms (prems, conc) = patternAtoms conc ++
                                        (concat (map patternAtoms prems))
        ruleAtoms = concat $ map rulePatternAtoms (map snd rules)
        allAtoms = nub $ axiomAtoms ++ ruleAtoms

        patternFormulas (ants ::=> sucs) = concat $ map formulas ants ++ map formulas sucs
        axiomFormulas = concat $ map patternFormulas (map snd axioms)
        rulePatternFormulas (prems, conc) = patternFormulas conc ++
                                        (concat (map patternFormulas prems))
        ruleFormulas = concat $ map rulePatternFormulas (map snd rules)
        allFormulas = nub $ axiomFormulas ++ ruleFormulas

        patternSets (ants ::=> sucs) = concat $ map contexts ants ++ map contexts sucs
        axiomSets = concat $ map patternSets (map snd axioms)
        rulePatternSets (prems, conc) = patternSets conc ++
                                        (concat (map patternSets prems))
        ruleSets = concat $ map rulePatternSets (map snd rules)
        allSets = nub $ axiomSets ++ ruleSets

        atomString = case allAtoms of
          [] -> ""
          [p] -> p ++ " is an atom"
          allAtoms -> intercalate ", " allAtoms ++ " are atoms"

        formulaString = case allFormulas of
          [] -> ""
          [a] -> a ++ " is an arbitrary formula"
          allFormulas -> intercalate ", " allFormulas ++ " are arbitrary formulas"

        contextString = case allSets of
          [] -> ""
          [gamma] -> gamma ++ " is an arbitrary list of formulas"
          allSets -> intercalate ", " allSets ++ " are arbitrary lists of formulas"

        qualString = let qualStrings = filter (not . null) [atomString,
                                                            formulaString,
                                                            contextString]
                     in case qualStrings of
                          [] -> ""
                          _  -> "where " ++ intercalate ",\n      " qualStrings
                          
instance Show Calculus where
  show = ppCalculus

-- | Pretty print a 'GoalSpec'.
ppGoalSpec :: GoalSpec -> String
ppGoalSpec [] = "top"
ppGoalSpec gs = intercalate "." (map show gs)



-- | \"Pretty\" print a derivation.
ppDerivation :: Derivation -> String
ppDerivation = ppDerivation' "" [] where
  ppDerivation' pad spec (Stub conclusion) =
    pad ++ show conclusion ++ " (unproved) [" ++ ppGoalSpec spec ++ "]\n"
  ppDerivation' pad spec (Axiom conclusion axiom) =
    pad ++ show conclusion ++ " (by " ++ axiom ++ ") [" ++ ppGoalSpec spec ++ "]\n"
  ppDerivation' pad spec (Der conclusion rule premises) =
    pad ++ show conclusion ++ " (by " ++ rule ++ ") [" ++ ppGoalSpec spec ++ "]\n" ++
    (concat $ ppPremises spec 1 premises)
    where ppPremises spec n [] = []
          ppPremises spec n (prem:prems) =
            ppDerivation' (pad++"  ") (spec ++ [n]) prem : ppPremises spec (n+1) prems

instance Show Derivation where
  show = ppDerivation

spliceStrings :: String -> String -> String
spliceStrings x y = unlines xyLines
  where xLines = lines x
        yLines = lines y
        (xLines', yLines') = sync xLines yLines
        xWidth = case xLines of (_:_) -> maximum (map length xLines)
                                _     -> 0
        yWidth = case yLines of (_:_) -> maximum (map length yLines)
                                _     -> 0
        xLines'' = map (extend xWidth) xLines'
        yLines'' = map (extend yWidth) yLines'
        xyLines = case (xWidth, yWidth) of
                    (0, _) -> yLines''
                    (_, 0) -> xLines''
                    _      -> zipWith (\l1 l2 -> l1 ++ sep ++ l2) xLines'' yLines''
        sync xs ys | length xs < length ys = (replicate (length ys - length xs) [] ++ xs, ys)
        sync xs ys | otherwise = (xs, replicate (length xs - length ys) [] ++ ys)
        extend 0 line   = line
        extend n []     = ' ' : extend (n-1) []
        extend n (x:xs) = x   : extend (n-1) xs
        sep = "   "

-- TODO: put this in some utility file
padL :: Int -> String -> String
padL n = (unlines . map (replicate n ' '++) . lines)

-- Pretty printing a derivation
-- TODO: put an asterisk at the current subgoal
-- TODO: maybe move some of these printing functions to a separate file (Main?)
ppDerivationTree' :: GoalSpec -> Derivation -> GoalSpec -> String
ppDerivationTree' subgoal (Stub conclusion) spec =
  show conclusion ++ if spec == subgoal then "*\n" else "\n"
ppDerivationTree' subgoal (Axiom conclusion axiom) spec =
  "[" ++ show conclusion ++ "]" ++ if spec == subgoal then "*\n" else "\n"
ppDerivationTree' subgoal (Der conclusion rule ders) spec =
  let newSpecs = zipWith (++) (repeat spec) (map (:[]) [1..length ders])
      ppDers = zipWith (ppDerivationTree' subgoal) ders newSpecs
      premString = foldl spliceStrings "" ppDers
      premStringWidth = case premString of (_:_) -> maximum (map length (lines premString))
                                           _     -> 0
      concString = show conclusion ++ if spec == subgoal then "*" else ""
      concStringWidth = length concString
      width = max premStringWidth concStringWidth
      premPad = (width - premStringWidth) `div` 2
      concPad = (width - concStringWidth) `div` 2
      premString' = padL premPad premString
      concString' = padL concPad concString
  in premString' ++ replicate concPad ' ' ++ replicate concStringWidth '-' ++
--     " (" ++ rule ++ ")\n" ++
     "\n" ++ concString'

-- | Pretty print a derivation as a tree in the typical style.
ppDerivationTree der subgoal = ppDerivationTree' subgoal der []

--------------------------------------------------------------------------------
-- examples

-- atom = PredPat "P"
-- a = FormPat "A"
-- b = FormPat "B"
-- c = FormPat "C"
-- gamma = SetPat "Gamma"
-- delta = SetPat "Delta"

x = VarTerm "x"
p = Pred "P"
q = Pred "Q"
r = Pred "R"
-- s = Pred "S" []
-- x = Pred "x" []
-- y = Pred "y" []
-- z = Pred "z" []
-- (%&) = And
-- (%|) = Or
-- (%>) = Implies
-- f <%> g = (f %> g) %& (g %> f)
-- neg a = Implies a Bottom
-- bot = Bottom

-- f1 = [q %> p, q] :=> [p]
-- f2 = [p] :=> [p]
-- f3 = [] :=> [p %> neg (neg p)]
-- f4 = [] :=> [((p %| q) %& ((p %> r) %& (q %> r))) %> r]
-- f5 = [] :=> [p %| neg p]
-- peirce = [] :=> [((p %> q) %> p) %> p]
-- demorgan1 = [] :=> [neg (p %& q) <%> (neg p %| neg q)]
-- em = [] :=> [p %| neg p]

-- pd = Stub ([] :=> [(p %& q) %> p])

--------------------------------------------------------------------------------
-- junk

-- | Produce a derivation of a sequent. This proof search procedure is very
-- inefficient at this stage, but it ought to find a derivation if there is one,
-- eventually. For a particular sequent, we pattern match against all the SequentPats
-- occurring in the conclusion of the rules of the input calculus; for each one that
-- matches, we attempt to instantiate the premises and derive the formula. If a rule
-- has any patterns in the premises that don't appear anywhere in the conclusion, the
-- rule will not be used.

-- derive :: Calculus     -- ^ The calculus we are using for this derivation.
--        -> Int          -- ^ Proof search depth.
--        -> Sequent      -- ^ The sequent to prove.
--        -> [Derivation] -- ^ A list of all obtainable derivations.
-- derive _ 0 _ = []
-- derive calculus n sequent = do
--   let axs = applicableAxioms calculus sequent
--   case axs of
--     (_:_) -> do
--       (name,_) <- axs
--       return $ Derivation sequent name []
--     _ -> do
--       (ruleName, assignment) <- applicableRules calculus sequent
--       let Just (premises,_) = lookup ruleName (rules calculus)
--       case sequence $ map (instSequentPat assignment) premises of
--         Just premiseInsts -> do
--           let premisesDerivations = map (derive calculus (n-1)) premiseInsts
--           derivationSet <- oneOfEach premisesDerivations
--           return $ Derivation sequent ruleName derivationSet
--         Nothing -> error $ "Ambiguous rule: " ++ ruleName
