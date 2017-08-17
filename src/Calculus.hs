{-|
Module      : Calculus
Description : Module for defining sequent calculi and constructing proofs within
              them.
Copyright   : (c) Ben Selfridge, 2017
License     : BSD3
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
  , UniName(..)
  , FormulaPat(..)
  , Sequent(..)
  , SequentPat(..)
  , RulePat(..)
  , FormulaAssignment
  , TermAssignment
  , Calculus(..)
  , UAbbrev(..)
  , BAbbrev(..)

  -- * Pattern matching
  , match
  , matchAll

  -- * Calculi functions
  , uAbbreviateForm
  , bAbbreviateForm
  , calcZeroaryOps
  , calcUnaryOps
  , calcBinaryOps
  , calcQts
  , instFormulaPat
  , instSequentPat

  -- * Derivations
  , Derivation(..)
  , GoalSpec(..)
  , stubs
  , getGoal
  , clearSubgoal
  , applicableAxioms
  , applicableRules
  , instAxiom
  , instRule
  , tryFormula
  , tryAxiom
  , tryRule
  , checkDerivation

  ) where

import Utils

import Data.List
import Data.Maybe

--------------------------------------------------------------------------------
-- | Represents a single term in predicate calculus.
data Term = ConstTerm String
          | VarTerm   String
          | AppTerm   String [Term]
  deriving (Eq)

-- TODO: remove this show instance, add it to PPCalculus.hs as a ppTerm function, and
-- add deriving (Show) to the data decl for Term.
instance Show Term where
  show (ConstTerm  c) = "_" ++ c
  show (VarTerm    v) = v
  show (AppTerm f ts) = f ++ "(" ++ intercalate ", " (map show ts) ++ ")"

--------------------------------------------------------------------------------
-- | Represents a single formula in predicate calculus.

data Formula = Pred String [Term]
             | ZeroaryOp { formulaOp :: UniName }
             -- ^ General 0-ary connective, like bottom.
             | UnaryOp { formulaOp :: UniName, formulaA :: Formula }
             -- ^ General 1-ary prefix connective, like negation or "box" in modal
             -- logic.
             | BinaryOp { formulaOp :: UniName
                        , formulaA  :: Formula
                        , formulaB  :: Formula
                        }
             -- ^ General 2-ary infix connective, like & or ->.
             | Quant { formulaQt :: UniName
                     , formulax  :: String
                     , formulaA  :: Formula
                     }
             -- ^ General quantified formula; forall or exists are the obvious ones.
  deriving (Eq, Show)

newtype UniName = UniName { getNames :: (String, String)
                            -- ^ first is ASCII, second is Unicode
                          }
  deriving (Eq, Show)

isZeroaryOp :: UniName -> Formula -> Bool
isZeroaryOp op (ZeroaryOp op') = op == op'
isZeroaryOp _ _ = False

isUnaryOp :: UniName -> Formula -> Bool
isUnaryOp op (UnaryOp op' _) = op == op'
isUnaryOp _ _ = False

isBinaryOp :: UniName -> Formula -> Bool
isBinaryOp op (BinaryOp op' _ _) = op == op'
isBinaryOp _ _ = False

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
  freeVars' (Pred _ ts)      = [ v | t <- ts, v <- termVars t ]
  freeVars' (ZeroaryOp _)    = []
  freeVars' (UnaryOp _ f)    = freeVars' f
  freeVars' (BinaryOp _ f g) = freeVars' f ++ freeVars' g
  freeVars' (Quant    _ x f) = [ v | v <- freeVars' f, v /= x ]

-- | Substitute a variable for a term inside a larger term.
substTerm :: String -> Term -> Term -> Term
substTerm x t (VarTerm    v) | x == v = t
substTerm x t (AppTerm f ts) = AppTerm f $ map (substTerm x t) ts
substTerm _ _ term = term

-- | Substitute a variable for a term inside a formula.
substFormula :: String -> Term -> Formula -> Formula
substFormula x t (Pred    p ts)     = Pred p $ map (substTerm x t) ts
substFormula _ _ (ZeroaryOp op)     = ZeroaryOp op
substFormula x t (UnaryOp op f)     = UnaryOp op (substFormula x t f)
substFormula x t (BinaryOp op f g)  = BinaryOp op (substFormula x t f) (substFormula x t g)
substFormula x t (Quant    qt y f)  | x == y    = Quant qt y f
                                    | otherwise = Quant qt y (substFormula x t f)

--------------------------------------------------------------------------------
-- | Represents a sequent in a Gentzen-style derivation. Logically, a sequent of the
-- form
--
-- > [f1, f2, ..., fn] :=> [g1, g2, ..., gm]
--
-- means the /conjunction/ of the f's implies the /disjunction/ of the g's, so if all of
-- the f's are true, then one of the g's must be true.

data Sequent = [Formula] :=> [Formula]
  deriving (Eq, Show)

--------------------------------------------------------------------------------
-- | A TermPat is a placeholder for a 'Term'.

data TermPat = VarPat  { termPatId :: String }
             -- ^ only match variables
             | TermPat { termPatId :: String }
             -- ^ match any term
  deriving (Eq, Show)

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

-- TODO: Add another pattern, ConcPredPat, with an explicit /list/ of
-- TermPats. Figure out how to extend all the matching and instantiation mechanisms
-- to this, and we will be able to add equality axioms to any calculus.

data FormulaPat = ZeroaryOpPat UniName
                | UnaryOpPat UniName FormulaPat
                | BinaryOpPat UniName FormulaPat FormulaPat
                -- ^ General binary connective. The UniName is the name for the
                -- operator, which provides both an ASCII and Unicode variant.
                | QuantPat UniName String FormulaPat
                -- ^ General quantifier. The UniName is the name for the operator, which
                -- provides both an ASCII and Unicode variant.
                | ConcPredPat String [TermPat]
                -- ^ Matches a particular atomic predicate or propositional variable,
                -- along with a list of term patterns.
                | PredPat String
                -- ^ Matches any atomic predicate or propositional variable.
                | FormPat String
                -- ^ Matches an /arbitrary/ formula
                | SetPat String
                -- ^ a /list/ of arbitrary formulas
                | SubstPat String TermPat String
                -- ^ substitute arg1 with arg2 in arg3
                | NoFreePat String FormulaPat
                -- ^ arg2 with no free variables matching arg1
  deriving (Eq, Show)

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
tryFormula formBindings termBindings (ConcPredPat p ts) =
  -- Just return a list of all the unbound terms in ts.
  ([], filter unboundTerm ts)
  where unboundTerm t = keyElem (termPatId t) termBindings
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
tryFormula _ _ (ZeroaryOpPat _) = ([], [])
tryFormula formBindings termBindings (UnaryOpPat _ s) = (sForms, sTerms) where
  (sForms, sTerms) = tryFormula formBindings termBindings s
tryFormula formBindings termBindings (BinaryOpPat _ s t) = (sForms ++ tForms, sTerms ++ tTerms) where
  (sForms, sTerms) = tryFormula formBindings termBindings s
  (tForms, tTerms) = tryFormula formBindings termBindings t
tryFormula formBindings termBindings (QuantPat _ x s) = (sForms, xTerms ++ sTerms) where
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
instFormulaPat _ termBindings (ConcPredPat p ts) = do
  ts' <- sequence $ map (\t -> lookup (termPatId t) termBindings) ts
  return [Pred p ts']
instFormulaPat formBindings _ (PredPat p) = lookup p formBindings
instFormulaPat formBindings _ (FormPat a) = lookup a formBindings
instFormulaPat formBindings _ (SetPat g)  = lookup g formBindings
instFormulaPat _ _      (ZeroaryOpPat op) = return [ZeroaryOp op]
instFormulaPat formBindings termBindings (UnaryOpPat op s) = do
  sB <- instFormulaPat formBindings termBindings s
  return [UnaryOp op s | s <- sB]
instFormulaPat formBindings termBindings (BinaryOpPat op s t) = do
  sB <- instFormulaPat formBindings termBindings s
  tB <- instFormulaPat formBindings termBindings t
  return [BinaryOp op a b | a <- sB, b <- tB]
instFormulaPat formBindings termBindings (QuantPat qt x s) = do
  -- TODO: check that this doesn't blow up if x doesn't map to a variable
  VarTerm y <- lookup x termBindings
  sB <- instFormulaPat formBindings termBindings s
  return [Quant qt y a | a <- sB]
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
  tryFormulas' formBindings termBindings ants `appendPair`
  tryFormulas' formBindings termBindings sucs
  where tryFormulas' formBindings termBindings pats =
          concatPairs $ map (tryFormula formBindings termBindings) pats

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

-- TODO: figure out the right way to map an outer pattern over an internal set
-- pattern to do something like !Gamma.
match :: [FormulaPat] -> [Formula] -> [(FormulaAssignment,TermAssignment)]
match (ZeroaryOpPat op:pats) fs = do
  [matchRest | ZeroaryOp op' <- nub fs
             , op == op'
             , fs' <- [delete (ZeroaryOp op) fs]
             , matchRest <- match pats fs']
match ((UnaryOpPat op pat):pats) fs =
  [(mergeForms, mergeTerms) | fs' <- nub $ powerset $ filter (isUnaryOp op) fs
                            , (aForms, aTerms) <- match [pat] (map formulaA fs')
                            , (matchForms, matchTerms) <- match pats (fs \\ fs')
                            , mergeForms <- mergeFormulaAssignments [aForms, matchForms]
                            , mergeTerms <- mergeTermAssignments [aTerms, matchTerms]]
match ((BinaryOpPat op pat1 pat2):pats) fs =
  [(mergeForms, mergeTerms) | fs' <- nub $ powerset $ filter (isBinaryOp op) fs
                            , (aForms, aTerms) <- match [pat1] (map formulaA fs')
                            , (bForms, bTerms) <- match [pat2] (map formulaB fs')
                            , (matchForms, matchTerms) <- match pats (fs \\ fs')
                            , mergeForms <- mergeFormulaAssignments [aForms, bForms, matchForms]
                            , mergeTerms <- mergeTermAssignments [aTerms, bTerms, matchTerms]]
match ((QuantPat qt x pat):pats) fs =
  [(mergeForms, mergeTerms) | Quant qt' y f <- nub fs
                            , qt == qt'
                            , (fForms, fTerms) <- match [pat] [f]
                            , (matchForms, matchTerms) <- match pats (delete (Quant qt y f) fs)
                            , mergeForms <- mergeFormulaAssignments [fForms, matchForms]
                            , mergeTerms <- mergeTermAssignments [[(x, VarTerm y)], fTerms, matchTerms]]
match ((ConcPredPat p ts):pats) fs =
  [(matchForms, matchTerms) | Pred p' ts' <- nub fs
                            , p == p'
                            , length ts == length ts'
                            , (matchForms, matchTerms) <- match pats (delete (Pred p' ts') fs)]
match ((PredPat p):pats) fs =
  [(mergeForms, matchTerms) | Pred p' ts <- nub fs
                            , (matchForms, matchTerms) <- match pats (delete (Pred p' ts) fs)
                            , mergeForms <- mergeFormulaAssignments [[(p, [Pred p' ts])], matchForms]]
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
--               , [botpat, gamma] ::=> [c]))p
--   ]}
-- @
data Calculus = Calculus { calcName :: String
                         , axioms   :: [(String, SequentPat)]
                         , rules    :: [(String, RulePat)]
                         , uAbbrevs :: [UAbbrev]
                         , bAbbrevs :: [BAbbrev]
                         }

extractSingleton :: [a] -> Maybe a
extractSingleton [x] = Just x
extractSingleton _   = Nothing

-- | This will be used for parsing and printing abbreviations of formulas. We provide
-- an example for abbreviating negation.
data UAbbrev = UAbbrev { uAbbrevOp  :: UniName
                       -- ^ = UniName ("~", "¬"), the unary prefix symbol for the
                       -- abbreviation
                       , uAbbrevA   :: String
                       -- ^ = "A", the name of the formula involved in the abbreviation
                       , uAbbrevPat :: FormulaPat
                       -- ^ = impliesPat (FormPat "A") bottomPat, where impliesPat
                       -- and bottomPat are suitably-defined functions
                       }
  deriving Show

-- | Given a formula f and a unary abbreviation, try and match f against the
-- abbreviation; if the match succeeds, return the formula that uAbbrevA should be
-- bound to, along with the original UAbbrev (this is for convenience). (TODO: give
-- example for negation)
uAbbrevMatch :: Formula -> UAbbrev -> Maybe (UAbbrev, Formula)
uAbbrevMatch f abb@(UAbbrev op a pat) = do
  (formBindings, termBindings) <- extractSingleton $ match [pat] [f]
  gs <- instFormulaPat formBindings termBindings (FormPat a)
  g  <- extractSingleton gs
  return $ (abb, g)

uAbbreviateForm :: Calculus -> Formula -> Maybe (UAbbrev, Formula)
uAbbreviateForm calc f = extractSingleton $ catMaybes $ map (uAbbrevMatch f) (uAbbrevs calc)

data BAbbrev = BAbbrev { bAbbrevOp  :: UniName
                       , bAbbrevA   :: String
                       , bAbbrevB   :: String
                       , bAbbrevPat :: FormulaPat
                       }
  deriving Show

bAbbrevMatch :: Formula -> BAbbrev -> Maybe (BAbbrev, Formula, Formula)
bAbbrevMatch f abb@(BAbbrev op a b pat) = do
  (formBindings, termBindings) <- extractSingleton $ match [pat] [f]
  gs <- instFormulaPat formBindings termBindings (FormPat a)
  hs <- instFormulaPat formBindings termBindings (FormPat b)
  g <- extractSingleton gs
  h <- extractSingleton hs
  return $ (abb, g, h)

bAbbreviateForm :: Calculus -> Formula -> Maybe (BAbbrev, Formula, Formula)
bAbbreviateForm calc f = extractSingleton $ catMaybes $ map (bAbbrevMatch f) (bAbbrevs calc)

-- TODO: Expand this to look at the axioms too!
calcFormulaPats :: Calculus -> [FormulaPat]
calcFormulaPats calc = forms where
  rulePats = map snd (rules calc)
  formPats = concat $ map (\(prems, conc) -> conc : prems) rulePats
  forms    = concat $ map (\(ants ::=> sucs) -> ants ++ sucs) formPats

formPatZeroaryOps :: FormulaPat -> [UniName]
formPatZeroaryOps (ZeroaryOpPat op)     = [op]
formPatZeroaryOps (UnaryOpPat _ f)      = formPatZeroaryOps f
formPatZeroaryOps (BinaryOpPat _ f1 f2) = formPatZeroaryOps f1 ++ formPatZeroaryOps f2
formPatZeroaryOps (QuantPat _ _ f)      = formPatZeroaryOps f
formPatZeroaryOps (NoFreePat _ f)       = []
formPatZeroaryOps _                     = []

calcZeroaryOps :: Calculus -> [UniName]
calcZeroaryOps calc = nub $ concat $ map formPatZeroaryOps (calcFormulaPats calc)

formPatUnaryOps :: FormulaPat -> [UniName]
formPatUnaryOps (UnaryOpPat op f)     = op : formPatUnaryOps f
formPatUnaryOps (BinaryOpPat _ f1 f2) = formPatUnaryOps f1 ++ formPatUnaryOps f2
formPatUnaryOps (QuantPat _ _ f)      = formPatUnaryOps f
formPatUnaryOps (NoFreePat _ f)       = formPatUnaryOps f
formPatUnaryOps _                     = []

calcUnaryOps :: Calculus -> [UniName]
calcUnaryOps calc = nub $ concat $ map formPatUnaryOps (calcFormulaPats calc)

formPatBinaryOps :: FormulaPat -> [UniName]
formPatBinaryOps (BinaryOpPat op f1 f2) = op : (formPatBinaryOps f1 ++ formPatBinaryOps f2)
formPatBinaryOps (UnaryOpPat _ f)       = formPatBinaryOps f
formPatBinaryOps (QuantPat _ _ f)       = formPatBinaryOps f
formPatBinaryOps (NoFreePat _ f)        = formPatBinaryOps f
formPatBinaryOps _                      = []

calcBinaryOps :: Calculus -> [UniName]
calcBinaryOps calc = nub $ concat $ map formPatBinaryOps (calcFormulaPats calc)

formPatQts :: FormulaPat -> [UniName]
formPatQts (UnaryOpPat _ f)      = formPatQts f
formPatQts (BinaryOpPat _ f1 f2) = formPatQts f1 ++ formPatQts f2
formPatQts (QuantPat qt _ f)     = qt : formPatQts f
formPatQts (NoFreePat _ f)       = formPatQts f
formPatQts _                     = []

calcQts :: Calculus -> [UniName]
calcQts calc = nub $ concat $ map formPatQts (calcFormulaPats calc)

--------------------------------------------------------------------------------
-- | (Partial) derivation of a sequent

data Derivation = Stub  { conclusion :: Sequent }
                | Axiom { conclusion :: Sequent
                        , axiomName  :: String
                        , forms      :: FormulaAssignment
                        , terms      :: TermAssignment
                        }
                | Der   { conclusion :: Sequent
                        , ruleName   :: String
                        , forms      :: FormulaAssignment
                        , terms      :: TermAssignment
                        , prems      :: [Derivation]
                        }
  deriving (Eq)

-- | Return all applicable axioms for a sequent. Gives the name of the axiom, and
-- the assignment that will match the formula to the conclusion of the axiom.
applicableAxioms :: Calculus -> Sequent -> [(String, FormulaAssignment, TermAssignment)]
applicableAxioms calculus (ants :=> sucs) = do
  (name, antPats ::=> sucPats) <- axioms calculus
  (formBinding, termBinding) <- matchAll [(antPats, ants), (sucPats, sucs)]
  return (name, formBinding, termBinding)

-- | Return all applicable rules for a sequent. Gives the name of the rule, and
-- the assignment that will match the formula to the conclusion of the rule. Note
-- that in general, this function does not provide the entire assignment that would
-- be necessary to actually instantiate the rule. If the premise of the rule contains
-- patterns that don't appear anywhere in the conclusion (like in a cut rule, for
-- instance), then we will need an assignment for that pattern before we can apply
-- the rule. Additionally, if the premise contains any term patterns that don't
-- appear in the conclusion, those will need to be added to the term assignment in
-- order to apply the rule.
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

-- | Given a 'Calculus', a axiom name, a 'GoalSpec' (pointer to a particular node in
-- the derivation tree), and a 'Derivation', return a new derivation consisting of
-- the old one with the given node replaced with an axiom application. Fails if the
-- node doesn't exist.

-- | Given a calculus, an axiom of that calculus, and an assignment, return a list of
-- all the unbound variables in the axiom.
tryAxiom :: Calculus -> String -> FormulaAssignment -> TermAssignment -> ([FormulaPat],[TermPat])
tryAxiom calculus name formBindings termBindings = case pat of
  Nothing -> ([],[])
  Just sequent -> trySequent formBindings termBindings sequent
  where pat = lookup name (axioms calculus)

-- TODO: for instAxiom and instRule, make it impossible to instantiate a rule where
-- hte ops or quantifiers don't exactly match
instAxiom :: Calculus -> String -> FormulaAssignment -> TermAssignment -> GoalSpec -> Derivation -> Maybe Derivation
instAxiom calculus name formBindings termBindings (x:xs) (Der sequent rule fb tb ders) = do
  der <- ders !!! (x-1)
  newDer <- instAxiom calculus name formBindings termBindings xs der
  return $ Der sequent rule fb tb (setElt (x-1) newDer ders)
instAxiom calculus name formBindings termBindings [] der = do
  axPat  <- lookup name (axioms calculus)
  axInst <- instSequentPat formBindings termBindings axPat
  -- Notice that even though we are not using axInst, we are implicitly using it
  -- because if the above assignment yield a Nothing (because the instantiation was
  -- invalid), then the result of instAxiom will be Nothing. I only gave it a name
  -- to be explicit.
  return $ Axiom (conclusion der) name formBindings termBindings

-- | Given a calculus, a rule of that calculus, and an assignment, return a list of
-- all the unbound variables in the rule.
tryRule :: Calculus -> String -> FormulaAssignment -> TermAssignment -> ([FormulaPat],[TermPat])
tryRule calculus name formBindings termBindings = case pat of
  Nothing -> ([],[])
  Just (prems, conc) ->
    let (rstForms, rstTerms) = concatPairs $ map (trySequent formBindings termBindings) prems
        (forms, terms) = trySequent formBindings termBindings conc
    in nubPair (forms ++ rstForms, terms ++ rstTerms)
  where pat = lookup name (rules calculus)

-- | Given a 'Calculus', a rule name, an assignment for the rule, a 'GoalSpec'
-- (pointer to a particular node in the derivation tree), and a 'Derivation', return
-- a new derivation consisting of the old one with the given node replaced with a
-- rule application. Fails if the node doesn't exist, or if instantation (via
-- instSequentPat) fails.
instRule :: Calculus -> String -> FormulaAssignment -> TermAssignment -> GoalSpec -> Derivation -> Maybe Derivation
instRule calculus name formBindings termBindings [] der = do
  (prems, conc) <- lookup name (rules calculus)
  premInsts <- sequence $ map (instSequentPat formBindings termBindings) prems
  concInst <- instSequentPat formBindings termBindings conc
  -- Notice that even though we are not using concInst, we are implicitly using it
  -- because if the above assignment yield a Nothing (because the instantiation was
  -- invalid), then the result of instRule will be Nothing. I only gave it a name to
  -- be explicit.
  return $ Der (conclusion der) name formBindings termBindings (map Stub premInsts)
instRule calculus name formBindings termBindings (x:xs) (Der sequent rule fb tb ders) = do
  der <- ders !!! (x-1)
  newDer <- instRule calculus name formBindings termBindings xs der
  return $ Der sequent rule fb tb (setElt (x-1) newDer ders)

clearSubgoal :: GoalSpec -> Derivation -> Maybe Derivation
clearSubgoal [] d = return $ Stub (conclusion d)
clearSubgoal (i:is) (Der seq rule fb tb ders) = do
  der    <- ders !!! (i-1)
  newDer <- clearSubgoal is der
  return $ Der seq rule fb tb (setElt (i-1) newDer ders)

-- | Given a "Calculus" and a "Derivation", check that the derivation is valid.
checkDerivation :: Calculus -> Derivation -> Either Derivation ()
checkDerivation calculus (Stub _) = return ()
checkDerivation calculus d@(Axiom conc axiomName formBindings termBindings)
  | Just d' <- instAxiom calculus axiomName formBindings termBindings [] d = return ()
  | otherwise = Left d
checkDerivation calculus d@(Der conc ruleName formBindings termBindings _)
  | Just d' <- instRule calculus ruleName formBindings termBindings [] d =
      if map conclusion (prems d) == map conclusion (prems d')
      then mapM_ (checkDerivation calculus) (prems d)
      else Left d
  | otherwise = Left d

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
