{-|
Module      : Calculus
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
  , clearSubgoal
  , applicableAxioms
  , applicableRules
  , applyAxiom
  , applyRule
  , tryAxiom
  , tryRule
--  , checkDerivation
  
  ) where

import Utils

import Data.List
import Data.Maybe

-- TODO: There is no real reason to have specific and, or, implies, etc. We can
-- abstract that to generalized connectives with different arities. 

--------------------------------------------------------------------------------
-- | Represents a single term in predicate calculus.
data Term = ConstTerm String
          | VarTerm   String
          | AppTerm   String [Term]
  deriving (Eq)

--------------------------------------------------------------------------------
-- | Represents a single formula in predicate calculus.
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

-- | All the variables in a term.
termVars :: Term -> [String]
termVars (ConstTerm  _) = []
termVars (VarTerm    v) = [v]
termVars (AppTerm _ ts) = [ v | t <- ts, v <- termVars t ]

-- | All the free variables in a formula.
freeVars :: Formula -> [String]
freeVars = nub . freeVars' where
  freeVars' Bottom = []
  freeVars' (Pred _ ts)   = [ v | t <- ts, v <- termVars t ]
  freeVars' (And     f g) = freeVars' f ++ freeVars' g
  freeVars' (Or      f g) = freeVars' f ++ freeVars' g
  freeVars' (Implies f g) = freeVars' f ++ freeVars' g
  freeVars' (Forall  x f) = [ v | v <- freeVars' f, v /= x ]
  freeVars' (Exists  x f) = [ v | v <- freeVars' f, v /= x ]

-- | Substitute a variable for a term inside a larger term.
substTerm :: String -> Term -> Term -> Term
substTerm x t (VarTerm    v) | x == v = t
substTerm x t (AppTerm f ts) = AppTerm f $ map (substTerm x t) ts
substTerm _ _ term = term

-- | Substitute a variable for a term inside a formula.
substFormula :: String -> Term -> Formula -> Formula
substFormula _ _ Bottom         = Bottom
substFormula x t (Pred    p ts) = Pred p $ map (substTerm x t) ts
substFormula x t (And     f g)  = And     (substFormula x t f) (substFormula x t g)
substFormula x t (Or      f g)  = Or      (substFormula x t f) (substFormula x t g)
substFormula x t (Implies f g)  = Implies (substFormula x t f) (substFormula x t g)
substFormula x t (Forall  y f)  | x == y    = Forall y f
                                | otherwise = Forall y (substFormula x t f)
substFormula x t (Exists  y f)  | x == y    = Exists y f
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
-- | A 'FormulaPat' is a placeholder for a 'Formula' or a list of 'Formula's. There is
-- a formula for each connective (_|_, &, |, ->, forall, exists), which matches
-- against any formula of that shape. There is a pattern called 'PredPat', which
-- matches against any atomic formula, or predicate. 'FormPat' is a wildcard, matching
-- against any /single/ formula. 'SetPat' matches against any /multiset/ of
-- formulas. 'SubstPat' acts like a wildcard in pattern matching, but in
-- instantiation it forces you to actually make a substitution. NoFreePat is like a
-- container for a pattern, and generates an obligation upon instantiation that
-- whatever the interior pattern is matched too must not contain any free occurences
-- of a particular variable.

data FormulaPat = BottomPat
             | AndPat FormulaPat FormulaPat
             | OrPat FormulaPat FormulaPat
             | ImpliesPat FormulaPat FormulaPat
             | ForallPat String FormulaPat
             | ExistsPat String FormulaPat
             | PredPat String
             | FormPat String
             -- ^ an /arbitrary/ formula
             | SetPat String
             -- ^ a /list/ of arbitrary formulas
             | SubstPat String TermPat String
             -- ^ substitute arg1 with arg2 in arg3
             | NoFreePat String FormulaPat
             -- ^ arg2 with no free variables matching arg1
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

-- | Given an assignment and a formula pattern, return a list of all the patterns in
-- the formula that are unbound. Use this in conjunction with instFormulaPat.
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

-- | Given /complete/ formula and term assignments, and a formula pattern attempt to
-- instantiate the pattern. This function should not be invoked on incomplete
-- assignments. By complete, we mean that every schematic variable on the formula and
-- term levels should have corresponding bindings in the first arguments provided for
-- this function.
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

-- | Same as tryFormula, but for SequentPats.
trySequent :: FormulaAssignment -> TermAssignment -> SequentPat -> ([FormulaPat], [TermPat])
trySequent formBindings termBindings (ants ::=> sucs) =
  tryFormulas' formBindings termBindings ants `appendPair` tryFormulas' formBindings termBindings sucs
  where tryFormulas' formBindings termBindings pats = concatPairs $ map (tryFormula formBindings termBindings) pats

-- | Same as instFormulaPat, but for SequentPats.
instSequentPat :: FormulaAssignment -> TermAssignment -> SequentPat -> Maybe Sequent
instSequentPat formBindings termBindings (ants ::=> sucs) = do
  antsInsts <- sequence (map (instFormulaPat formBindings termBindings) ants)
  sucsInsts <- sequence (map (instFormulaPat formBindings termBindings) sucs)
  return $ concat antsInsts :=> concat sucsInsts

--------------------------------------------------------------------------------
-- Matching patterns

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
match (BottomPat:pats) fs =
  [matchRest | Bottom    <- nub fs
             , fs'       <- [delete Bottom fs]
             , matchRest <- match pats fs']
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
match ((PredPat p):pats) fs =
  [(merge, matchTerms) | Pred p' ts <- nub fs
                       , (matchForms, matchTerms) <- match pats (delete (Pred p' ts) fs)
                       , merge <- mergeFormulaAssignments [[(p, [Pred p' ts])], matchForms]]
match ((FormPat n):pats) fs =
  [(mergeForms, matchTerms) | y <- nub fs
                            , (matchForms, matchTerms) <- match pats (delete y fs)
                            , mergeForms <- mergeFormulaAssignments [[(n,[y])], matchForms]]
match ((SetPat s):pats) fs =
  [(mergeForms, matchTerms) | fs' <- nub $ powerset fs
                            , (matchForms, matchTerms) <- match pats (fs \\ fs')
                            , mergeForms <- mergeFormulaAssignments [[(s,fs')], matchForms]]
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
-- | (Partial) derivation of a sequent

data Derivation = Stub  Sequent
                | Axiom Sequent String FormulaAssignment TermAssignment
                | Der   Sequent String FormulaAssignment TermAssignment [Derivation]

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
stubs (Stub sequent)       = [([], sequent)]
stubs (Axiom _ _ _ _)      = []
stubs (Der   _ _ _ _ ders) = concat $ numberAll 1 $ map stubs ders
  where 
    number n (goalSpec, sequent) = (n:goalSpec, sequent)
    numberAll n [] = []
    numberAll n (x:xs) = map (number n) x : numberAll (n+1) xs

-- | Given a 'GoalSpec' and a 'Derivation', traverse the derivation tree and find the sub-derivation
-- pointed to by that 'GoalSpec'.
getGoal :: GoalSpec -> Derivation -> Maybe Derivation
getGoal [] der = Just der
getGoal (x:xs) (Der _ _ _ _ ders) = do
  der <- ders !!! (x-1)
  getGoal xs der
getGoal _ _ = Nothing

-- | Get the conclusion of a derivation (the sequent that appears underneath the line).
conclusion :: Derivation -> Sequent
conclusion (Stub  sequent)         = sequent
conclusion (Axiom sequent _ _ _)   = sequent
conclusion (Der   sequent _ _ _ _) = sequent

setElt :: Int -> a -> [a] -> [a]
setElt _ _ [] = []
setElt 0 x (y:ys) = x : ys
setElt n x (y:ys) | n > 0 = y : (setElt (n-1) x ys)

-- | Given a 'Calculus', a axiom name, a 'GoalSpec' (pointer to a particular node in
-- the derivation tree), and a 'Derivation', return a new derivation consisting of
-- the old one with the given node replaced with an axiom application. Fails if the
-- node doesn't exist.

-- TODO: actually check the applicability here. We don't want to have to assume the
-- axiom is applicable; after all, it does return a Maybe Derivation, and we can use
-- the fact that this /checks/ applicability in the proof checking procedure.
applyAxiom :: Calculus -> String -> FormulaAssignment -> TermAssignment -> GoalSpec -> Derivation -> Maybe Derivation
applyAxiom calculus name formBindings termBindings [] (Stub sequent) = do
  axPat  <- lookup name (axioms calculus)
  axInst <- instSequentPat formBindings termBindings axPat
  return $ Axiom sequent name formBindings termBindings
applyAxiom calculus name formBindings termBindings (x:xs) (Der sequent rule fb tb ders) = do
  der <- ders !!! (x-1)
  newDer <- applyAxiom calculus name formBindings termBindings xs der
  return $ Der sequent rule fb tb (setElt (x-1) newDer ders)

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
-- rule application. Fails if the node doesn't exist, or if instantation (via
-- instSequentPat) fails.
applyRule :: Calculus -> String -> FormulaAssignment -> TermAssignment -> GoalSpec -> Derivation -> Maybe Derivation
applyRule calculus name formBindings termBindings [] der = do
  (prems, conc) <- lookup name (rules calculus)
  premInsts <- sequence $ map (instSequentPat formBindings termBindings) prems
  concInst <- instSequentPat formBindings termBindings conc
  return $ Der (conclusion der) name formBindings termBindings (map Stub premInsts)
applyRule calculus name formBindings termBindings (x:xs) (Der sequent rule fb tb ders) = do
  der <- ders !!! (x-1)
  newDer <- applyRule calculus name formBindings termBindings xs der
  return $ Der sequent rule fb tb (setElt (x-1) newDer ders)

-- | Given a calculus, a rule of that calculus, and an assignment, return a list of
-- all the unbound variables in the rule.
tryRule :: Calculus -> String -> FormulaAssignment -> TermAssignment -> ([FormulaPat],[TermPat])
tryRule calculus name formBindings termBindings = case pat of
  Nothing -> ([],[])
  Just (prems, conc) ->
    nubPair $ trySequent formBindings termBindings conc `appendPair` concatPairs (map (trySequent formBindings termBindings) prems)
  where pat = lookup name (rules calculus)

clearSubgoal :: GoalSpec -> Derivation -> Maybe Derivation
clearSubgoal [] (Stub seq)          = return $ Stub seq
clearSubgoal [] (Axiom seq _ _ _)   = return $ Stub seq
clearSubgoal [] (Der   seq _ _ _ _) = return $ Stub seq
clearSubgoal (i:is) (Der seq rule fb tb ders) = do
  der    <- ders !!! (i-1)
  newDer <- clearSubgoal is der
  return $ Der seq rule fb tb (setElt (i-1) newDer ders)

-- TODO: fix this
-- | Given a "Calculus" and a "Derivation", check that the derivation is valid.
-- checkDerivation :: Calculus -> Derivation -> Either Derivation ()
-- checkDerivation calculus (Stub _) = return ()
-- checkDerivation calculus d@(Axiom conc axiom formBindings termBindings)
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
