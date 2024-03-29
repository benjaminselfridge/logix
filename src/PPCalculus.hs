{-|
Module      : PPCalculus
Description : Pretty printing.
Copyright   : (c) Ben Selfridge, 2017
License     : BSD3
Maintainer  : benselfridge@gmail.com
Stability   : experimental

-}

module PPCalculus
  ( -- * Pretty printing
    ppFormula
  , ppFormulaList
  , ppSequent
  , ppFormulaPat
  , ppSequentPat
  , ppFormulaInst
  , ppSequentInst
  , ppRulePat
  , ppGoalSpec
  , ppCalculus
  , ppDerivation
  , ppDerivationTree
  ) where

import Calculus
import Utils

import Data.List (nub, intercalate)

--------------------------------------------------------------------------------
-- pretty printing

sq = UniName ("=>","⇒")

-- | Pretty print a term.
ppTerm :: Term -> String
ppTerm (VarTerm    v) = v
ppTerm (AppTerm f []) = f
ppTerm (AppTerm f ts) = f ++ "(" ++ intercalate ", " (map ppTerm ts) ++ ")"


-- | Pretty print a formula, with top level parentheses.
ppFormula' :: Bool -> Calculus -> Formula -> String
ppFormula' unicode calc f
  | Just (uAbbrev, f') <- uAbbreviateForm calc f =
      pickPair unicode (getNames $ uAbbrevOp uAbbrev) ++ ppFormula' unicode calc f'
  | Just (bAbbrev, f', g') <- bAbbreviateForm calc f =
      "(" ++ ppFormula' unicode calc f' ++
      " " ++ pickPair unicode (getNames $ bAbbrevOp bAbbrev) ++ " " ++
      ppFormula' unicode calc g' ++ ")"
ppFormula' unicode calc (Pred p [])   = p
ppFormula' unicode calc (Pred p ts)   = p ++ "(" ++ intercalate ", " (map ppTerm ts) ++ ")"
ppFormula' unicode calc (ZeroaryOp op)    = pickPair unicode (getNames op)
ppFormula' unicode calc (UnaryOp op a) =
  pickPair unicode (getNames op) ++ ppFormula' unicode calc a
ppFormula' unicode calc (BinaryOp op a b) =
  "(" ++ ppFormula' unicode calc a ++
  " " ++ pickPair unicode (getNames op) ++ " " ++
  ppFormula' unicode calc b ++ ")"
ppFormula' unicode calc (Quant qt x a) =
  pickPair unicode (getNames qt) ++ x ++ "." ++ ppFormula' unicode calc a

-- | Pretty print a formula, omitting top level parentheses.
ppFormula :: Bool -> Calculus -> Formula -> String
ppFormula unicode calc f
  | Just (uAbbrev, f') <- uAbbreviateForm calc f =
      pickPair unicode (getNames $ uAbbrevOp uAbbrev) ++ ppFormula' unicode calc f'
  | Just (bAbbrev, f', g') <- bAbbreviateForm calc f =
      ppFormula' unicode calc f' ++
      " " ++ pickPair unicode (getNames $ bAbbrevOp bAbbrev) ++ " " ++
      ppFormula' unicode calc g'
ppFormula unicode calc (BinaryOp op a b) =
  ppFormula' unicode calc a ++ " " ++ pickPair unicode (getNames op) ++ " " ++ ppFormula' unicode calc b
ppFormula unicode calc formula = ppFormula' unicode calc formula

-- | Pretty print a list of formulas.
ppFormulaList :: Bool -> Calculus -> [Formula] -> String
ppFormulaList unicode calc = intercalate ", " . map (ppFormula unicode calc)

-- | Pretty print a sequent.
ppSequent :: Bool -> Calculus -> Sequent -> String
ppSequent unicode calc (ants :=> sucs) = intercalate ", " (map (ppFormula unicode calc) ants) ++
                                         " " ++ pickPair unicode (getNames sq) ++ " " ++
                                         intercalate ", " (map (ppFormula unicode calc) sucs)

-- TODO: g3ip_em, => P | ~P leads to a listing of <P> -> _|_. Figure out why this is
-- happening and how to render it as ~<P>.

-- | Pretty print a term pattern
ppTermPat :: TermPat -> String
ppTermPat (AppPat f []) = f
ppTermPat (AppPat f ts) = f ++ "(" ++ intercalate ", " (map ppTermPat ts) ++ ")"
ppTermPat t = termPatId t

-- | Pretty print a formula pattern, with top level parentheses.

-- TODO: I am removing the [no free ] tag because it looks like shit, but we might
-- want to display the no free pattern in ppCalculus. Perhaps as a one-liner
-- immediately below the rule.
ppFormulaPat' :: Bool -> FormulaPat -> String
ppFormulaPat' unicode (ConcPredPat p []) = p
ppFormulaPat' unicode (ConcPredPat p ts) = p ++ "(" ++ intercalate ", " (map ppTermPat ts) ++ ")"
ppFormulaPat' unicode (PredPat p) = p
ppFormulaPat' unicode (FormPat a) = a
ppFormulaPat' unicode (SetPat gamma) = gamma
ppFormulaPat' unicode (ZeroaryOpPat op) = pickPair unicode (getNames op)
ppFormulaPat' unicode (UnaryOpPat op s) = pickPair unicode (getNames op) ++ ppFormulaPat' unicode s
ppFormulaPat' unicode (BinaryOpPat op s t) =
  "(" ++ ppFormulaPat' unicode s ++
  " " ++ pickPair unicode (getNames op) ++ " " ++
  ppFormulaPat' unicode t ++ ")"
ppFormulaPat' unicode (QuantPat qt x s) =
  pickPair unicode (getNames qt) ++ x ++ ".(" ++ ppFormulaPat' unicode s ++ ")"
ppFormulaPat' unicode (SubstPat x t a) = a ++ "(" ++ ppTermPat t ++ "/" ++ x ++ ")"
ppFormulaPat' unicode (NoFreePat x s) = ppFormulaPat' unicode s

-- | Pretty print a formula pattern, omitting top level parentheses.
ppFormulaPat :: Bool -> FormulaPat -> String
ppFormulaPat unicode (BinaryOpPat op s t) =
  ppFormulaPat' unicode s ++
  " " ++ pickPair unicode (getNames op) ++ " " ++
  ppFormulaPat' unicode t
ppFormulaPat unicode f = ppFormulaPat' unicode f

-- | Pretty print a sequent pattern.
ppSequentPat unicode (ants ::=> sucs) =
  intercalate ", " (map (ppFormulaPat unicode)  ants) ++
  " " ++ pickPair unicode (getNames sq) ++ " " ++
  intercalate ", " (map (ppFormulaPat unicode)  sucs)

-- | Pretty print a (possibly incomplete) instantiation of a term pattern.
ppTermInst :: TermAssignment -> TermPat -> String
ppTermInst termBindings (AppPat f []) = f
ppTermInst termBindings (AppPat f ts) =
  f ++ "(" ++ intercalate ", " (map (ppTermInst termBindings) ts) ++ ")"
ppTermInst termBindings t = case lookup (termPatId t) termBindings of
  Nothing -> "<" ++ termPatId t ++ ">"
  Just t' -> ppTerm t'

-- | Pretty print a (possibly incomplete) instantiation of a formula pattern.

-- TODO: removed the [no free] tag in printing a formula inst, but we might want to
-- give the user some feedback when they try and instantiate the pattern
-- incorrectly.
-- TODO: does this handle abbreviations correctly?
-- TODO: when we have a SetPat inside a UnaryOpPat, we need to somehow map the unary
-- op over the setpat. I think the solution is really to return a *list* of strings
-- from ppFormulaInst', and map the operator over the list. However, we still have to
-- think about how to do this for BinaryOps...
ppFormulaInst' :: Bool -> Calculus -> FormulaAssignment -> TermAssignment -> FormulaPat -> [String]
ppFormulaInst' unicode calc formBindings termBindings (ConcPredPat p []) = [p]
ppFormulaInst' unicode calc formBindings termBindings (ConcPredPat p ts) =
  [p ++ "(" ++ intercalate ", " (map (ppTermInst termBindings) ts) ++ ")"]
ppFormulaInst' unicode calc formBindings termBindings (PredPat p) = case lookup p formBindings of
  Nothing  -> ["<" ++ p ++ ">"] -- p is unbound
  Just [f] -> [ppFormula' unicode calc f]
  Just fs  -> error $ "atom variable " ++ p ++ " bound to " ++ ppFormulaList unicode calc fs
ppFormulaInst' unicode calc formBindings termBindings (FormPat a) = case lookup a formBindings of
  Nothing  -> ["<" ++ a ++ ">"]
  Just [f] -> [ppFormula' unicode calc f]
  Just fs  -> error $ "var variable " ++ a ++ " bound to " ++ ppFormulaList unicode calc fs
ppFormulaInst' unicode calc formBindings termBindings (SetPat g) = case lookup g formBindings of
  Nothing -> ["<" ++ g ++ ">"]
  Just fs -> map (ppFormula' unicode calc) fs -- show the formulas
ppFormulaInst' unicode calc formBindings termBindings (ZeroaryOpPat op) =
  [pickPair unicode (getNames op)]
ppFormulaInst' unicode calc formBindings termBindings (UnaryOpPat op s) =
  map (pickPair unicode (getNames op) ++) $ ppFormulaInst' unicode calc formBindings termBindings s
ppFormulaInst' unicode calc formBindings termBindings (BinaryOpPat op s t) =
  ["(" ++ a ++ " " ++ pickPair unicode (getNames op) ++ " " ++ b ++ ")" |
    a <- ppFormulaInst' unicode calc formBindings termBindings s
  , b <- ppFormulaInst' unicode calc formBindings termBindings t]
ppFormulaInst' unicode calc formBindings termBindings (QuantPat qt x s) =
  case lookup x termBindings of
    Nothing ->
      map (((pickPair unicode (getNames qt)) ++ "<" ++  x ++ ">.") ++) $
      ppFormulaInst' unicode calc formBindings termBindings s
    Just (VarTerm y) ->
      map (((pickPair unicode (getNames qt)) ++ y ++ ".") ++) $
      ppFormulaInst' unicode calc formBindings termBindings s
ppFormulaInst' unicode calc formBindings termBindings (SubstPat x t s) =
  let xStr = ppTermInst termBindings (VarPat x)
      tStr = ppTermInst termBindings t
      sStr = case lookup s formBindings of
               Nothing -> "<" ++ s ++ ">"
               Just s' -> ppFormulaList unicode calc s'
  in [sStr ++ "(" ++ tStr ++ "/" ++ xStr ++ ")"]
ppFormulaInst' unicode calc formBindings termBindings (NoFreePat x s) =
  case lookup x termBindings of
    Nothing -> ppFormulaInst' unicode calc formBindings termBindings s
    Just (VarTerm y) -> ppFormulaInst' unicode calc formBindings termBindings s

-- | Given a (possibly incomplete) assignment and a formula pattern, pretty print the
-- instantiation.

-- TODO: Add another case for FormPat, NoFreePat and SubstPat, where we look up the
-- binding. NoFreePat and SubstPat should call the non-quoted ppFormulaInst
-- recursively.
ppFormulaInst :: Bool -> Calculus -> FormulaAssignment -> TermAssignment -> FormulaPat -> [String]
-- Maybe add another case for SetPat where we look up the thing directly and call
-- ppFormula on it.
ppFormulaInst unicode calc formBindings termBindings (BinaryOpPat op s t) =
  [a ++ " " ++ pickPair unicode (getNames op) ++ " " ++ b |
    a <- ppFormulaInst' unicode calc formBindings termBindings s
  , b <- ppFormulaInst' unicode calc formBindings termBindings t]
  -- ["(" ++ a ++ " " ++ pickPair unicode (getNames op) ++ " " ++ b ++ ")" |
  --   a <- ppFormulaInst' unicode calc formBindings termBindings s
  -- , b <- ppFormulaInst' unicode calc formBindings termBindings t]
ppFormulaInst unicode calc formBindings termBindings (FormPat a) =
  case lookup a formBindings of
    Nothing   -> ["<" ++ a ++ ">"]
    Just [f]  -> [ppFormula unicode calc f]
    Just fs   -> error $ "ppFormulaInst: variable bound to multiple formulas" ++ ppFormulaList unicode calc fs
ppFormulaInst unicode calc formBindings termBindings (SetPat g) =
  case lookup g formBindings of
    Nothing -> ["<" ++ g ++ ">"]
    Just fs -> map (ppFormula unicode calc) fs
ppFormulaInst unicode calc formBindings termBindings pat = ppFormulaInst' unicode calc formBindings termBindings pat

-- | Given a (possibly incomplete) assignment and a sequent pattern, pretty print the
-- instantiation.
ppSequentInst :: Bool -> Calculus -> FormulaAssignment -> TermAssignment -> SequentPat -> String
ppSequentInst unicode calc formBindings termBindings (ants ::=> sucs) =
  intercalate ", " (filter (not . null) (combineStrs ants)) ++
  " " ++ pickPair unicode (getNames sq) ++ " " ++
  intercalate ", " (filter (not . null) (combineStrs sucs))
  where foldfn strs a =
          strs ++ ppFormulaInst unicode calc formBindings termBindings a
        combineStrs = foldl foldfn []

-- | Pretty print a rule pattern.
ppRulePat :: Bool -> String -> (String, RulePat) -> String
ppRulePat unicode pad (name, (premises, conclusion)) =
  let pStr = intercalate "   " (map (ppSequentPat unicode) premises)
      pWidth = length pStr
      cStr = ppSequentPat unicode conclusion
      cWidth = length cStr
      totalWidth = max pWidth cWidth
      pPad = (totalWidth - pWidth) `div` 2
      cPad = (totalWidth - cWidth) `div` 2
  in pad ++ replicate pPad ' ' ++ pStr ++ "\n" ++
     pad ++ replicate totalWidth '-' ++ " (" ++ name ++ ")\n" ++
     pad ++ replicate cPad ' ' ++ cStr

atoms :: FormulaPat -> [String]
atoms (PredPat p) = [p]
atoms (BinaryOpPat _ s t) = atoms s ++ atoms t
atoms _ = []

formulas :: FormulaPat -> [String]
formulas (FormPat a) = [a]
formulas (BinaryOpPat _ s t) = formulas s ++ formulas t
formulas _ = []

contexts :: FormulaPat -> [String]
contexts (SetPat a) = [a]
contexts (BinaryOpPat _ s t) = contexts s ++ contexts t
contexts _ = []

-- TODO: add variables and terms to the "where" clause
-- TODO: display "NoFree" patterns more elegantly, maybe with some kind of footnote.
ppCalculus :: Bool -> Calculus -> String
ppCalculus unicode (Calculus name axioms rules uAbbrevs bAbbrevs) =
  "Calculus " ++ name ++ ".\n\n" ++
  "Axioms:\n" ++ concat (map showAxiom axioms) ++ "\n" ++
  "Rules:\n\n" ++ concat (map showRule rules) ++
  qualString

  where showAxiom (axiomName, axiomPattern) =
          "  " ++ ppSequentPat unicode axiomPattern ++ " (" ++ axiomName ++ ")\n"
        showRule rule = ppRulePat unicode "  " rule ++ "\n\n"

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
          [p] -> p ++ " is an atomic formula (predicate)"
          allAtoms -> intercalate ", " allAtoms ++ " are atomic formulas (predicates)"

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

-- | Pretty print a 'GoalSpec'.
ppGoalSpec :: GoalSpec -> String
ppGoalSpec [] = "top"
ppGoalSpec gs = intercalate "." (map show gs)

-- | \"Pretty\" print a derivation.

ppDerivation :: Bool -> Calculus -> Derivation -> String
ppDerivation unicode calc = ppDerivation' unicode "" [] where
  ppDerivation' unicode pad spec (Stub conclusion) =
    pad ++ "+ " ++ ppSequent unicode calc conclusion ++ " (unproved) [" ++ ppGoalSpec spec ++ "]\n"
  ppDerivation' unicode pad spec (Axiom conclusion axiom _ _) =
    pad ++ "+ " ++ ppSequent unicode calc conclusion ++ " (by " ++ axiom ++ ") [" ++ ppGoalSpec spec ++ "]\n"
  ppDerivation' unicode pad spec (Der conclusion rule _ _ premises) =
    pad ++ "+ " ++ ppSequent unicode calc conclusion ++ " (by " ++ rule ++ ") [" ++ ppGoalSpec spec ++ "]\n" ++
    (concat $ ppPremises spec 1 premises)
    where ppPremises spec n [] = []
          ppPremises spec n (prem:prems) =
            ppDerivation' unicode (pad++"  ") (spec ++ [n]) prem : ppPremises spec (n+1) prems

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
        sep = " | "

padL :: Int -> String -> String
padL n = (unlines . map (replicate n ' '++) . lines)

-- Pretty printing a derivation as a tree
ppDerivationTree' :: Bool -> Calculus -> GoalSpec -> Derivation -> GoalSpec -> String
ppDerivationTree' unicode calc subgoal (Stub conclusion) spec =
  ppSequent unicode calc conclusion ++ if spec == subgoal then "*\n" else "\n"
ppDerivationTree' unicode calc subgoal (Axiom conclusion axiom _ _) spec =
  let concString = ppSequent unicode calc conclusion ++ if spec == subgoal then "*" else ""
      width = length concString
  in replicate width '-' ++ "\n" ++ concString ++ "\n"
ppDerivationTree' unicode calc subgoal (Der conclusion rule _ _ ders) spec =
  let newSpecs = zipWith (++) (repeat spec) (map (:[]) [1..length ders])
      ppDers = zipWith (ppDerivationTree' unicode calc subgoal) ders newSpecs
      premString = foldl spliceStrings "" ppDers
      premStringWidth = case premString of (_:_) -> maximum (map length (lines premString))
                                           _     -> 0
      concString = ppSequent unicode calc conclusion ++ if spec == subgoal then "*" else ""
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
ppDerivationTree :: Bool -> Calculus -> Derivation -> GoalSpec -> String
ppDerivationTree unicode calc der subgoal = ppDerivationTree' unicode calc subgoal der []
