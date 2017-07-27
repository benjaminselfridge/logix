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
    Formula(..)
  , FormulaPat(..)
  , Sequent(..)
  , SequentPat(..)
  , Assignment
  , Calculus(..)
  , showFormulaInst
  , showSequentInst
  
  -- * Pattern operators
  , ($&), ($|), ($>), negpat, botpat

  -- * Pattern matching
  , match
  , matchAll

  -- * Derivations
  , Derivation(..)
  , GoalSpec(..)
  , conclusion
  , stubs
  , getGoal
  , showGoalSpec
  , applicableAxioms
  , applicableRules
  , applyAxiom
  , applyRule
  , tryAxiom
  , tryRule
  , checkDerivation
  
  -- * Pretty printing
  , ppRulePat
  , ppDerivation
  , ppDerivationTree
  
  -- * Example calculi
  , g3ip
  , g3cp
  , g0ip
  , g0ip_em
  , g3ipm
  , hilbert
  ) where

import Data.List
import Data.Maybe

--------------------------------------------------------------------------------
-- | Represents a single formula in propositional calculus.
data Formula = Bottom
             | Atom String
             | And Formula Formula
             | Or Formula Formula
             | Implies Formula Formula
  deriving (Eq, Ord)

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
-- | A FormulaPat is a placeholder for a 'Formula' or a list of 'Formula's. 

data FormulaPat = BottomPat
             | AtomPat String
             | AndPat FormulaPat FormulaPat
             | OrPat FormulaPat FormulaPat
             | ImpliesPat FormulaPat FormulaPat
             | VarPat String
             -- ^ an /arbitrary/ formula
             | SetPat String
             -- ^ a /list/ of arbitrary formulas
  deriving (Eq)

-- | Infix AndPat.
($&) = AndPat

-- | Infix OrPat.
($|) = OrPat

-- | Infix ImpliesPat.
($>) = ImpliesPat

-- | Negated pattern.
negpat pat = pat $> botpat

-- | Bottom pattern.
botpat = BottomPat

--------------------------------------------------------------------------------
-- | Pattern for a sequent.
data SequentPat = [FormulaPat] ::=> [FormulaPat]

-- | Pattern for a rule: a list of premises at the top, and a conclusion at the
-- bottom. 
type RulePat = ([SequentPat], SequentPat)

--------------------------------------------------------------------------------
-- | Map from identifiers to concrete formulas. 
type Assignment = [(String, [Formula])]

instFormulaPat :: Assignment -> FormulaPat -> Maybe [Formula]
instFormulaPat _        BottomPat    = return [Bottom]
instFormulaPat bindings (AtomPat p)  = lookup p bindings
instFormulaPat bindings (VarPat a)   = lookup a bindings
instFormulaPat bindings (SetPat g)   = lookup g bindings
instFormulaPat bindings (AndPat s t) = do
  sB <- instFormulaPat bindings s
  tB <- instFormulaPat bindings t
  return [And a b | a <- sB, b <- tB]
instFormulaPat bindings (OrPat s t) = do
  sB <- instFormulaPat bindings s
  tB <- instFormulaPat bindings t
  return [Or a b | a <- sB, b <- tB]
instFormulaPat bindings (ImpliesPat s t) = do
  sB <- instFormulaPat bindings s
  tB <- instFormulaPat bindings t
  return [Implies a b | a <- sB, b <- tB]

instSequentPat :: Assignment -> SequentPat -> Maybe Sequent
instSequentPat bindings (ants ::=> sucs) = do
  antsInsts <- sequence (map (instFormulaPat bindings) ants)
  sucsInsts <- sequence (map (instFormulaPat bindings) sucs)
  return $ concat antsInsts :=> concat sucsInsts

-- given an assignment and a formula pattern, return a list of all the patterns in
-- the formula that are unbound.
tryFormula :: Assignment -> FormulaPat -> [FormulaPat]
tryFormula _ BottomPat = []
tryFormula bindings (AtomPat p) = case lookup p bindings of
                                    Nothing -> [AtomPat p]
                                    Just _  -> []
tryFormula bindings (VarPat  p) = case lookup p bindings of
                                    Nothing -> [VarPat p]
                                    Just _  -> []
tryFormula bindings (SetPat  p) = case lookup p bindings of
                                    Nothing -> [SetPat p]
                                    Just _  -> []
tryFormula bindings (AndPat     s t) = svars ++ tvars where
  svars = tryFormula bindings s
  tvars = tryFormula bindings t
tryFormula bindings (OrPat      s t) = svars ++ tvars where
  svars = tryFormula bindings s
  tvars = tryFormula bindings t
tryFormula bindings (ImpliesPat s t) = svars ++ tvars where
  svars = tryFormula bindings s
  tvars = tryFormula bindings t


trySequent :: Assignment -> SequentPat -> [FormulaPat]
trySequent bindings (ants ::=> sucs) =
  nub $ tryFormulas' bindings ants ++ tryFormulas' bindings sucs
  where tryFormulas' bindings pats = concat $ map (tryFormula bindings) pats

--------------------------------------------------------------------------------
-- Matching patterns

-- | powerset of a list, viewed as a multiset.
powerset :: [a] -> [[a]]
powerset (x:xs) = [ x : px | px <- pxs ] ++ pxs
  where pxs = powerset xs
powerset [] = [[]]

-- | merge two assignments if they are in agreement; otherwise return Nothing
mergeAssignments :: [Assignment] -> [Assignment]
mergeAssignments (((n, cs):a1):assigns) = do
  mergeRest <- mergeAssignments (a1:assigns)
  case lookup n mergeRest of
    Nothing -> return $ (n, cs) : mergeRest
    Just cs' | cs == cs' -> return mergeRest
    _ -> []
mergeAssignments ([]:assigns) = mergeAssignments assigns
mergeAssignments [] = return []
  
-- | Take a list of patterns and a list of formulas to match, and produce a list
-- of all satisfying assignments.
match :: [FormulaPat] -> [Formula] -> [Assignment]
match (BottomPat:pats) fs =
  [matchRest | Bottom    <- nub fs
             , fs'       <- [delete Bottom fs]
             , matchRest <- match pats fs']
match ((VarPat n):pats) fs =
  [merge | y          <- nub fs
         , assignRest <- match pats (delete y fs)
         , merge      <- mergeAssignments [[(n,[y])], assignRest]]
match ((AtomPat p):pats) fs =
  [merge | Atom p'    <- nub fs
         , assignRest <- match pats (delete (Atom p') fs)
         , merge      <- mergeAssignments [[(p, [Atom p'])], assignRest]]
match ((AndPat pat1 pat2):pats) fs =
  [merge | And c1 c2  <- nub fs
         , matchc1    <- match [pat1] [c1]
         , matchc2    <- match [pat2] [c2]
         , assignRest <- match pats (delete (And c1 c2) fs)
         , merge      <- mergeAssignments [matchc1, matchc2, assignRest]]
match ((OrPat pat1 pat2):pats) fs =
  [merge | Or c1 c2   <- nub fs
         , matchc1    <- match [pat1] [c1]
         , matchc2    <- match [pat2] [c2]
         , assignRest <- match pats (delete (Or c1 c2) fs)
         , merge      <- mergeAssignments [matchc1, matchc2, assignRest]]
match ((ImpliesPat pat1 pat2):pats) fs =
  [merge | Implies c1 c2 <- nub fs
         , matchc1       <- match [pat1] [c1]
         , matchc2       <- match [pat2] [c2]
         , assignRest    <- match pats (delete (Implies c1 c2) fs)
         , merge         <- mergeAssignments [matchc1, matchc2, assignRest]]
match ((SetPat s):pats) fs =
  [merge | fs'        <- nub $ powerset fs
         , assignRest <- match pats (fs \\ fs')
         , merge      <- mergeAssignments [[(s,fs')], assignRest]]
match [] [] = [[]]
match [] _ = []

oneOfEach :: [[a]] -> [[a]]
oneOfEach ((x:xs):rst) = [ x : l | l <- oneOfEach rst ] ++ oneOfEach (xs:rst)
oneOfEach ([]:rst) = []
oneOfEach [] = [[]]

-- | Given a list of constraints, produce all assignments that satisfy every
-- constraint.
matchAll :: [([FormulaPat], [Formula])] -> [Assignment]
matchAll pairs = do
  let matchPairs = map (uncurry match) pairs
  assignments <- oneOfEach matchPairs
  mergeAssignments assignments

--------------------------------------------------------------------------------
-- | Gentzen-style calculus, defined using patterns. Example use:
--
-- @
--
-- atom = AtomPat \"P\"
-- a = VarPat \"A\"
-- b = VarPat \"B\"
-- c = VarPat \"C\"
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
  deriving (Show)

-- | Return all applicable axioms for a sequent. Gives the name of the axiom, and
-- the assignment that will match the formula to the conclusion of the axiom.
applicableAxioms :: Calculus -> Sequent -> [(String, Assignment)]
applicableAxioms calculus (ants :=> sucs) = do
  (name, antPats ::=> sucPats) <- axioms calculus
  assignment <- matchAll [(antPats, ants), (sucPats, sucs)]
  return (name, assignment)

-- | Return all applicable rules for a sequent. Gives the name of the rule, and
-- the assignment that will match the formula to the conclusion of the rule.
applicableRules :: Calculus -> Sequent -> [(String, Assignment)]
applicableRules calculus (ants :=> sucs) = do
  (name, (_, antPats ::=> sucPats)) <- rules calculus
  assignment <- matchAll [(antPats, ants), (sucPats, sucs)]
  return (name, assignment)

type GoalSpec = [Int]

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

getGoal :: GoalSpec -> Derivation -> Maybe Derivation
getGoal [] der = Just der
getGoal (x:xs) (Der _ _ ders) = do
  der <- ders !!! (x-1)
  getGoal xs der
getGoal _ _ = Nothing

conclusion :: Derivation -> Sequent
conclusion (Stub  sequent)     = sequent
conclusion (Axiom sequent _)   = sequent
conclusion (Der   sequent _ _) = sequent

setElt :: Int -> a -> [a] -> [a]
setElt _ _ [] = []
setElt 0 x (y:ys) = x : ys
setElt n x (y:ys) | n > 0 = y : (setElt (n-1) x ys)

applyAxiom :: Calculus -> String -> GoalSpec -> Derivation -> Maybe Derivation
applyAxiom calculus name [] (Stub sequent) = Just $ Axiom sequent name
applyAxiom calculus name (x:xs) (Der sequent rule ders) = do
  der <- ders !!! (x-1)
  newDer <- applyAxiom calculus name xs der
  return $ Der sequent rule (setElt (x-1) newDer ders)

-- | Given a calculus, an axiom of that calculus, and an assignment, return a list of
-- all the unbound variables in the axiom.
tryAxiom :: Calculus -> String -> Assignment -> [FormulaPat]
tryAxiom calculus name assignment = case pat of
  Nothing -> []
  Just sequent -> trySequent assignment sequent
  where pat = lookup name (axioms calculus)

applyRule :: Calculus -> String -> Assignment -> GoalSpec -> Derivation -> Maybe Derivation
applyRule calculus name assignment [] der = do
  (premises, antPats ::=> sucPats) <- lookup name (rules calculus)
  premiseInsts <- sequence $ map (instSequentPat assignment) premises
  return $ Der (conclusion der) name (map Stub premiseInsts)
applyRule calculus name assignment (x:xs) (Der sequent rule ders) = do
  der <- ders !!! (x-1)
  newDer <- applyRule calculus name assignment xs der
  return $ Der sequent rule (setElt (x-1) newDer ders)

-- | Given a calculus, a rule of that calculus, and an assignment, return a list of
-- all the unbound variables in the rule.
tryRule :: Calculus -> String -> Assignment -> [FormulaPat]
tryRule calculus name assignment = case pat of
  Nothing -> []
  Just (prems, conc) ->
    nub $ trySequent assignment conc ++ concat (map (trySequent assignment) prems)
  where pat = lookup name (rules calculus)

checkDerivation :: Calculus -> Derivation -> Either Derivation ()
checkDerivation calculus (Stub _) = return ()
checkDerivation calculus d@(Axiom conc axiom)
  | Just (lax ::=> rax) <- lookup axiom (axioms calculus)
  , (l :=> r) <- conc = do
      let matches = matchAll [(lax, l), (rax, r)]
      case matches of
        [] -> Left d
        _  -> return ()
checkDerivation calculus d@(Der conc rule prems)
  | Just (rulePrems, ruleConc) <- lookup rule (rules calculus)
  , formulas <- foldl (++) [] (map (\(l  :=> r) -> [l,r]) (conc:map conclusion prems))
  , patterns <- foldl (++) [] (map (\(l ::=> r) -> [l,r]) (ruleConc:rulePrems)) = do
      mapM_ (checkDerivation calculus) prems
      let matches = matchAll (zipAll patterns formulas)
          -- use zipAll to make sure we 
      case matches of
        [] -> Left d
        _ -> return ()
  where zipAll (a:as) (b:bs) = (a,b)  : zipAll as bs
        zipAll (a:as) []     = (a,[]) : zipAll as []
        zipAll []     (b:bs) = ([],b) : zipAll [] bs
        zipAll []     []     = []
checkDerivation _ d = Left d -- rule not found

--------------------------------------------------------------------------------
-- show instances

-- TODO: clean all this shit up somehow

showFormula' Bottom        = "_|_"
showFormula' (Atom p)      = p
showFormula' (And (Implies a b) (Implies b' a'))
  | a == a', b == b'       = "(" ++ showFormula' a ++ " <-> " ++ showFormula' b ++ ")"
showFormula' (And a b)     = "(" ++ showFormula' a ++ " & "   ++ showFormula' b ++ ")"
showFormula' (Or a b)      = "(" ++ showFormula' a ++ " | "   ++ showFormula' b ++ ")"
showFormula' (Implies a Bottom)
                           = "~" ++ showFormula' a
showFormula' (Implies a b) = "(" ++ showFormula' a ++ " -> "  ++ showFormula' b ++ ")"

instance Show Formula where
  show (And (Implies a b) (Implies b' a'))
    | a == a', b == b'     = showFormula' a ++ " <-> " ++ showFormula' b
  show (And a b)          = showFormula' a ++ " & " ++ showFormula' b
  show (Or a b)           = showFormula' a ++ " | " ++ showFormula' b
  show (Implies a Bottom) = "~" ++ showFormula' a
  show (Implies a b)      = showFormula' a ++ " -> " ++ showFormula' b
  show formula            = showFormula' formula

instance Show Sequent where
  show (ants :=> sucs) = intercalate ", " (map show ants) ++ " => " ++
                         intercalate ", " (map show sucs)

-- TODO: parenthesize patterns, just like Formula
showFormulaPat' (AtomPat p) = p
showFormulaPat' (VarPat a) = a
showFormulaPat' (SetPat gamma) = gamma
showFormulaPat' (AndPat (ImpliesPat s t) (ImpliesPat t' s'))
  | s == s' && t == t' = "(" ++ showFormulaPat' s ++ " <-> " ++ showFormulaPat' t ++ ")"
showFormulaPat' (AndPat     s t) = "(" ++ showFormulaPat' s ++ " & "  ++ showFormulaPat' t ++ ")"
showFormulaPat' (OrPat      s t) = "(" ++ showFormulaPat' s ++ " | "  ++ showFormulaPat' t ++ ")"
showFormulaPat' (ImpliesPat s BottomPat) = "~" ++ showFormulaPat' s
showFormulaPat' (ImpliesPat s t) = "(" ++ showFormulaPat' s ++ " -> " ++ showFormulaPat' t ++ ")"
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

showFormulaInst' :: Assignment -> FormulaPat -> String
showFormulaInst' bindings (AtomPat p) = case lookup p bindings of
  Nothing  -> "[[" ++ p ++ "]]" -- p is unbound
  Just [f] -> show f
  Just fs  -> error $ "atom variable " ++ p ++ " bound to " ++ show fs
showFormulaInst' bindings (VarPat a) = case lookup a bindings of
  Nothing  -> "[[" ++ a ++ "]]"
  Just [f] -> show f
  Just fs  -> error $ "var variable " ++ a ++ " bound to " ++ show fs
showFormulaInst' bindings (SetPat g) = case lookup g bindings of
  Nothing -> "[[" ++ g ++ "]]"
  Just fs -> intercalate ", " (map show fs) -- show the formulas
showFormulaInst' bindings (AndPat (ImpliesPat s t) (ImpliesPat t' s'))
  | s == s' && t == t' =
    "(" ++ showFormulaInst' bindings s ++ " <-> " ++ showFormulaInst' bindings t ++ ")"
showFormulaInst' bindings (AndPat s t) =
  "(" ++ showFormulaInst' bindings s ++ " & " ++ showFormulaInst' bindings t ++ ")"
showFormulaInst' bindings (OrPat s t) =
  "(" ++ showFormulaInst' bindings s ++ " | " ++ showFormulaInst' bindings t ++ ")"
showFormulaInst' bindings (ImpliesPat s BottomPat) = "~" ++ showFormulaInst' bindings s
showFormulaInst' bindings (ImpliesPat s t) =
  "(" ++ showFormulaInst' bindings s ++ " -> " ++ showFormulaInst' bindings t ++ ")"
showFormulaInst' bindings BottomPat = "_|_"

showFormulaInst :: Assignment -> FormulaPat -> String
showFormulaInst bindings (AndPat (ImpliesPat s t) (ImpliesPat t' s'))
  | s == s' && t == t' =
    showFormulaInst' bindings s ++ " <-> " ++ showFormulaInst' bindings t
showFormulaInst bindings (AndPat s t) =
  showFormulaInst' bindings s ++ " & " ++ showFormulaInst' bindings t
showFormulaInst bindings (OrPat s t) =
  showFormulaInst' bindings s ++ " | " ++ showFormulaInst' bindings t
showFormulaInst bindings (ImpliesPat s BottomPat) = "~" ++ showFormulaInst' bindings s
showFormulaInst bindings (ImpliesPat s t) =
  showFormulaInst' bindings s ++ " -> " ++ showFormulaInst' bindings t
showFormulaInst bindings pat = showFormulaInst' bindings pat

showSequentPat' (ants ::=> sucs) = intercalate ", " (map show ants) ++ " => " ++
                                   intercalate ", " (map show sucs)

instance Show SequentPat where
  show = showSequentPat'

showSequentInst :: Assignment -> SequentPat -> String
showSequentInst bindings (ants ::=> sucs) =
  intercalate ", " (filter (not . null) (map (showFormulaInst bindings) ants)) ++
   " => " ++
  intercalate ", " (filter (not . null) (map (showFormulaInst bindings) sucs))

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
atoms (AtomPat p) = [p]
atoms (AndPat s t) = atoms s ++ atoms t
atoms (OrPat s t) = atoms s ++ atoms t
atoms (ImpliesPat s t) = atoms s ++ atoms t
atoms _ = []

formulas :: FormulaPat -> [String]
formulas (VarPat a) = [a]
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

        -- TODO: fix this.

        qualString' [] = ""
        qualString' ("":qs) = qualString' qs
        qualString' (q:[]) = "      " ++ q
        qualString' (q:qs) = "      " ++ q ++ ",\n" ++ qualString' qs

        qualString'' [] = ""
        qualString'' (q:[]) = q
        qualString'' ("":qs) = qualString'' qs
        qualString'' (q:qs) = q ++ ",\n" ++ qualString' qs

        qualString = case qualString'' [atomString, formulaString, contextString] of
          "" -> ""
          qStr -> "where " ++ qStr

instance Show Calculus where
  show = ppCalculus

showGoalSpec :: GoalSpec -> String
showGoalSpec [] = "top"
showGoalSpec gs = intercalate "." (map show gs)

-- TODO: make a pretty printer where each stub actually gets annotated with the
-- subgoal it corresponds to

ppDerivation :: Derivation -> String
ppDerivation = ppDerivation' "" [] where
  ppDerivation' pad spec (Stub conclusion) =
    pad ++ show conclusion ++ " (unproved) [" ++ showGoalSpec spec ++ "]\n"
  ppDerivation' pad spec (Axiom conclusion axiom) =
    pad ++ show conclusion ++ " (by " ++ axiom ++ ") [" ++ showGoalSpec spec ++ "]\n"
  ppDerivation' pad spec (Der conclusion rule premises) =
    pad ++ show conclusion ++ " (by " ++ rule ++ ") [" ++ showGoalSpec spec ++ "]\n" ++
    (concat $ ppPremises spec 1 premises)
    where ppPremises spec n [] = []
          ppPremises spec n (prem:prems) =
            ppDerivation' (pad++"  ") (spec ++ [n]) prem : ppPremises spec (n+1) prems

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

padL :: Int -> String -> String
padL n = (unlines . map (replicate n ' '++) . lines)

-- Pretty printing a derivation
-- TODO: put an asterisk at the current subgoal
-- TODO: maybe move some of these printing functions to a separate file (Main?)
ppDerivationTree' :: Derivation -> GoalSpec -> String
ppDerivationTree' (Stub conclusion) spec =
  show conclusion ++ "\n"
ppDerivationTree' (Axiom conclusion axiom) spec =
  "[" ++ show conclusion ++ "]\n"
ppDerivationTree' (Der conclusion rule ders) spec =
  let newSpecs = zipWith (++) (repeat spec) (map (:[]) [1..length ders])
      ppDers = zipWith ppDerivationTree' ders newSpecs
      premString = foldl spliceStrings "" ppDers
      premStringWidth = case premString of (_:_) -> maximum (map length (lines premString))
                                           _     -> 0
      concString = show conclusion
      concStringWidth = length concString
      width = max premStringWidth concStringWidth
      premPad = (width - premStringWidth) `div` 2
      concPad = (width - concStringWidth) `div` 2
      premString' = padL premPad premString
      concString' = padL concPad concString
  in premString' ++ padL concPad (replicate concStringWidth '-') ++ concString'

ppDerivationTree der = ppDerivationTree' der []
  
--------------------------------------------------------------------------------
-- Some definitions of Calculi

atom = AtomPat "P"
a = VarPat "A"
b = VarPat "B"
c = VarPat "C"
gamma = SetPat "Gamma"
delta = SetPat "Delta"

-- | G3ip, a contraction-free calculus for intuitionistic logic with shared
-- contexts. A good calculus for proof search of intuitionistic formulas.
g3ip :: Calculus
g3ip = Calculus {
  name = "g3ip",
  axioms = [("Axiom", [atom, gamma] ::=> [atom])],
  rules = 
  [ ("R&", ([ [gamma] ::=> [a], [gamma] ::=> [b] ],
            [gamma] ::=> [a $& b]))
  , ("R|1", ([ [gamma] ::=> [a] ],
             [gamma] ::=> [a $| b]))
  , ("R|2", ([ [gamma] ::=> [b] ],
             [gamma] ::=> [a $| b]))
  , ("R->", ([ [a, gamma] ::=> [b] ],
             [gamma] ::=> [a $> b]))
  , ("L&", ([ [a, b, gamma] ::=> [c] ],
            [a $& b, gamma] ::=> [c]))
  , ("L|", ([ [a, gamma] ::=> [c], [b, gamma] ::=> [c] ],
            [a $| b, gamma] ::=> [c]))
  , ("L->", ([ [a $> b, gamma] ::=> [a], [b, gamma] ::=> [c] ],
             [a $> b, gamma] ::=> [c]))
  , ("L_|_", ([],
              [botpat, gamma] ::=> [c]))
  ]}

-- | G0ip, a calculus for intuitionistic logic with independent contexts. Not a great
-- calculus for proof search due to the independent contexts, and the fact that we
-- usually need to explicitly use weakening and/or contraction in order to prove
-- simple formulas.
g0ip :: Calculus
g0ip = Calculus {
  name = "g0ip",
  axioms = [("Axiom", [atom] ::=> [atom])],
  rules =
  [ ("R&", ([ [gamma] ::=> [a], [delta] ::=> [b] ],
            [gamma, delta] ::=> [a $& b]))
  , ("R|1", ([ [gamma] ::=> [a] ],
             [gamma] ::=> [a $| b]))
  , ("R|2", ([ [gamma] ::=> [b] ],
             [gamma] ::=> [a $| b]))
  , ("R->", ([ [a, gamma] ::=> [b] ],
             [gamma] ::=> [a $> b]))
  , ("L&", ([ [a, b, gamma] ::=> [c] ],
            [a $& b, gamma] ::=> [c]))
  , ("L|", ([ [a, gamma] ::=> [c], [b, delta] ::=> [c] ],
            [a $| b, gamma, delta] ::=> [c]))
  , ("L->", ([ [gamma] ::=> [a], [b, delta] ::=> [c] ],
             [a $> b, gamma, delta] ::=> [c]))
  , ("L_|_", ([],
              [botpat] ::=> [c]))
  , ("Wk", ([ [gamma] ::=> [c] ],
            [a, gamma] ::=> [c]))
  , ("Ctr", ([ [a, a, gamma] ::=> [c] ],
             [a, gamma] ::=> [c]))
  ]}

-- | G0ip with the law of excluded middle, so a classical sequent calculus with
-- independent contexts.
g0ip_em :: Calculus
g0ip_em = Calculus {
  name = "g0ip_em",
  axioms = [("Axiom", [atom] ::=> [atom])],
  rules =
  [ ("R&", ([ [gamma] ::=> [a], [delta] ::=> [b] ],
            [gamma, delta] ::=> [a $& b]))
  , ("R|1", ([ [gamma] ::=> [a] ],
             [gamma] ::=> [a $| b]))
  , ("R|2", ([ [gamma] ::=> [b] ],
             [gamma] ::=> [a $| b]))
  , ("R->", ([ [a, gamma] ::=> [b] ],
             [gamma] ::=> [a $> b]))
  , ("L&", ([ [a, b, gamma] ::=> [c] ],
            [a $& b, gamma] ::=> [c]))
  , ("L|", ([ [a, gamma] ::=> [c], [b, delta] ::=> [c] ],
            [a $| b, gamma, delta] ::=> [c]))
  , ("L->", ([ [gamma] ::=> [a], [b, delta] ::=> [c] ],
             [a $> b, gamma, delta] ::=> [c]))
  , ("L_|_", ([],
              [botpat] ::=> [c]))
  , ("EM", ([ [atom, gamma] ::=> [c], [negpat atom, delta] ::=> [c] ],
            [gamma, delta] ::=> [c]))
  , ("Wk", ([ [gamma] ::=> [c] ],
            [a, gamma] ::=> [c]))
  , ("Ctr", ([ [a, a, gamma] ::=> [c] ],
             [a, gamma] ::=> [c]))
  ]}

-- | G3cp, a contraction-free calculus for classical logic with shared contexts. This
-- calculus is ideally suited for proof search, as any given sequent usually has at
-- most one rule that applies to it.
g3cp :: Calculus
g3cp = Calculus {
  name = "g3cp",
  axioms = [("Axiom", [atom, gamma] ::=> [delta, atom])],
  rules =
  [ ("L&", ([ [a, b, gamma] ::=> [delta] ],
            [a $& b, gamma] ::=> [delta]))
  , ("L|", ([ [a, gamma] ::=> [delta], [b, gamma] ::=> [delta] ],
            [a $| b, gamma] ::=> [delta]))
  , ("L->", ([ [gamma] ::=> [delta, a], [b, gamma] ::=> [delta] ],
             [a $> b, gamma] ::=> [delta]))
  , ("L_|_", ([],
              [botpat, gamma] ::=> [delta]))
  , ("R&", ([ [gamma] ::=> [delta, a], [gamma] ::=> [delta, b] ],
            [gamma] ::=> [delta, a $& b]))
  , ("R|", ([ [gamma] ::=> [delta, a, b] ],
            [gamma] ::=> [delta, a $| b]))
  , ("R->", ([ [a, gamma] ::=> [delta, b] ],
             [gamma] ::=> [delta, a $> b]))
  ]}

g3ipm :: Calculus
g3ipm = Calculus {
  name = "g3ipm",
  axioms = [("Axiom", [atom, gamma] ::=> [delta, atom])],
  rules =
  [ ("L&", ([ [a, b, gamma] ::=> [delta] ],
            [a $& b, gamma] ::=> [delta]))
  , ("L|", ([ [a, gamma] ::=> [delta], [b, gamma] ::=> [delta] ],
            [a $| b, gamma] ::=> [delta]))
  , ("L->", ([ [a $> b, gamma] ::=> [a], [b, gamma] ::=> [delta] ],
             [a $> b, gamma] ::=> [delta]))
  , ("L_|_", ([],
              [botpat, gamma] ::=> [delta]))
  , ("R&", ([ [gamma] ::=> [delta, a], [gamma] ::=> [delta, b] ],
            [gamma] ::=> [delta, a $& b]))
  , ("R|", ([ [gamma] ::=> [delta, a, b] ],
            [gamma] ::=> [delta, a $| b]))
  , ("R->", ([ [a, gamma] ::=> [b] ],
             [gamma] ::=> [delta, a $> b]))
  ]}

hilbert :: Calculus
hilbert = Calculus {
  name = "hilbert",
  axioms = [("H1", [] ::=> [a $> (b $> a)]),
            ("H2",  [] ::=> [(a $> b) $> ((a $> (b $> c)) $> (a $> c))]),
            ("H3", [] ::=> [negpat (negpat a) $> a])],
  rules = [("MP", ([ [] ::=> [a], [] ::=> [a $> b] ],
                   [] ::=> [b]))]
}

--------------------------------------------------------------------------------
-- examples

p = Atom "P"
q = Atom "Q"
r = Atom "R"
s = Atom "S"
x = Atom "x"
y = Atom "y"
z = Atom "z"
(%&) = And
(%|) = Or
(%>) = Implies
f <%> g = (f %> g) %& (g %> f)
neg a = Implies a Bottom
bot = Bottom

f1 = [q %> p, q] :=> [p]
f2 = [p] :=> [p]
f3 = [] :=> [p %> neg (neg p)]
f4 = [] :=> [((p %| q) %& ((p %> r) %& (q %> r))) %> r]
f5 = [] :=> [p %| neg p]
peirce = [] :=> [((p %> q) %> p) %> p]
demorgan1 = [] :=> [neg (p %& q) <%> (neg p %| neg q)]
em = [] :=> [p %| neg p]

pd = Stub ([] :=> [(p %& q) %> p])

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
