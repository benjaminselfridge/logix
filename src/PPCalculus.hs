module PPCalculus
    -- * Pretty printing
  ( ppFormula
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

--------------------------------------------------------------------------------
-- pretty printing

-- TODO: move all this to PPCalculus.hs

sq = UniName ("=>","⇒")

-- | Pretty print a formula, with top level parentheses.
ppFormula' :: Bool -> Formula -> String
ppFormula' unicode (Pred p [])   = p
ppFormula' unicode (Pred p ts)   = p ++ "(" ++ intercalate ", " (map show ts) ++ ")"
ppFormula' unicode (ZeroaryOp op)    = pickPair unicode (getNames op)
ppFormula' unicode (BinaryOp op a b) =
  "(" ++ ppFormula' unicode a ++
  " " ++ pickPair unicode (getNames op) ++ " " ++
  ppFormula' unicode b ++ ")"
ppFormula' unicode (Quant qt x a) = pickPair unicode (getNames qt) ++ x ++ "." ++ ppFormula' unicode a

-- | Pretty print a formula, omitting top level parentheses.
ppFormula :: Bool -> Formula -> String
ppFormula unicode (BinaryOp op a b) =
  ppFormula' unicode a ++ " " ++ pickPair unicode (getNames op) ++ " " ++ ppFormula' unicode b
ppFormula unicode formula = ppFormula' unicode formula

-- | Pretty print a list of formulas.
ppFormulaList :: Bool -> [Formula] -> String
ppFormulaList unicode = intercalate ", " . map (ppFormula unicode)

-- | Pretty print a sequent.
ppSequent :: Bool -> Sequent -> String
ppSequent unicode (ants :=> sucs) = intercalate ", " (map (ppFormula unicode)  ants) ++
                                    " " ++ pickPair unicode (getNames sq) ++ " " ++
                                    intercalate ", " (map (ppFormula unicode)  sucs)

-- TODO: g3i, top => ~exists x.P(x) -> forall x.~P(x) leads to a presentation of ~ as
-- -> _|_.

-- | Pretty print a formula pattern, with top level parentheses.
ppFormulaPat' :: Bool -> FormulaPat -> String
ppFormulaPat' unicode (PredPat p) = p
ppFormulaPat' unicode (FormPat a) = a
ppFormulaPat' unicode (SetPat gamma) = gamma
ppFormulaPat' unicode (ZeroaryOpPat op) = pickPair unicode (getNames op)
ppFormulaPat' unicode (BinaryOpPat op s t) =
  "(" ++ ppFormulaPat' unicode s ++
  " " ++ pickPair unicode (getNames op) ++ " " ++
  ppFormulaPat' unicode t ++ ")"
ppFormulaPat' unicode (QuantPat qt x s) =
  pickPair unicode (getNames qt) ++ x ++ ".(" ++ ppFormulaPat' unicode  s ++ ")"
ppFormulaPat' unicode (SubstPat x t a) = a ++ "(" ++ termPatId t ++ "/" ++ x ++ ")"
ppFormulaPat' unicode (NoFreePat x s) = ppFormulaPat' unicode s ++ "[no free " ++ x ++ "]"

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
  intercalate ", " (map (ppFormulaPat True)  sucs)

-- | Pretty print a (possibly incomplete) instantiation of a formula pattern.
ppFormulaInst' :: Bool -> FormulaAssignment -> TermAssignment -> FormulaPat -> String
ppFormulaInst' unicode formBindings termBindings (PredPat p) = case lookup p formBindings of
  Nothing  -> "<" ++ p ++ ">" -- p is unbound
  Just [f] -> ppFormula' unicode f
  Just fs  -> error $ "atom variable " ++ p ++ " bound to " ++ ppFormulaList unicode fs
ppFormulaInst' unicode formBindings termBindings (FormPat a) = case lookup a formBindings of
  Nothing  -> "<" ++ a ++ ">"
  Just [f] -> ppFormula' unicode f
  Just fs  -> error $ "var variable " ++ a ++ " bound to " ++ ppFormulaList unicode fs
ppFormulaInst' unicode formBindings termBindings (SetPat g) = case lookup g formBindings of
  Nothing -> "<" ++ g ++ ">"
  Just fs -> ppFormulaList unicode fs -- show the formulas
ppFormulaInst' unicode formBindings termBindings (ZeroaryOpPat op) = pickPair unicode (getNames op)
ppFormulaInst' unicode formBindings termBindings (BinaryOpPat op s t) =
  "(" ++ ppFormulaInst' unicode formBindings termBindings s ++
  " " ++ pickPair unicode (getNames op) ++ " " ++
  ppFormulaInst' unicode formBindings termBindings t ++ ")"
ppFormulaInst' unicode formBindings termBindings (QuantPat qt x s) =
  pickPair unicode (getNames qt) ++
  case lookup x termBindings of
    Nothing          -> "<" ++  x ++ ">." ++ ppFormulaInst' unicode formBindings termBindings s
    Just (VarTerm y) -> y ++ "." ++ ppFormulaInst' unicode formBindings termBindings s
ppFormulaInst' unicode formBindings termBindings (SubstPat x t s) =
  let xStr = case lookup x termBindings of
               Nothing -> "<" ++ x ++ ">"
               Just (VarTerm y) -> y
      tStr = case lookup (termPatId t) termBindings of
               Nothing -> "<" ++ termPatId t ++ ">"
               Just t' -> show t'
      sStr = case lookup s formBindings of
               Nothing -> "<" ++ s ++ ">"
               Just s' -> ppFormulaList unicode s'
  in sStr ++ "(" ++ tStr ++ "/" ++ xStr ++ ")"
ppFormulaInst' unicode formBindings termBindings (NoFreePat x s) =
  case lookup x termBindings of
    Nothing -> ppFormulaInst' unicode formBindings termBindings s ++ "[no free <" ++ x ++ "> ]"
    Just (VarTerm y) -> ppFormulaInst' unicode formBindings termBindings s ++ "[no free " ++ y ++ "]"

-- | Given a (possibly incomplete) assignment and a formula pattern, pretty print the
-- instantiation.

-- TODO: Add another case for FormPat, NoFreePat and SubstPat, where we look up the
-- binding. NoFreePat and SubstPat should call the non-quoted ppFormulaInst recursively.
ppFormulaInst :: Bool -> FormulaAssignment -> TermAssignment -> FormulaPat -> String
ppFormulaInst unicode formBindings termBindings (BinaryOpPat op s t) =
  ppFormulaInst' unicode formBindings termBindings s ++
  " " ++ pickPair unicode (getNames op) ++ " " ++
  ppFormulaInst' unicode formBindings termBindings t
ppFormulaInst unicode formBindings termBindings (FormPat a) =
  case lookup a formBindings of
    Nothing   -> "<" ++ a ++ ">"
    Just [f]  -> ppFormula unicode f
    _         -> error "ppFormulaInst: variable bound to multiple formulas"
ppFormulaInst unicode formBindings termBindings pat = ppFormulaInst' unicode formBindings termBindings pat

-- | Given a (possibly incomplete) assignment and a sequent pattern, pretty print the
-- instantiation.
ppSequentInst :: Bool -> FormulaAssignment -> TermAssignment -> SequentPat -> String
ppSequentInst unicode formBindings termBindings (ants ::=> sucs) =
  intercalate ", " (filter (not . null) (map (ppFormulaInst unicode formBindings termBindings) ants)) ++
  " " ++ pickPair unicode (getNames sq) ++ " " ++
  intercalate ", " (filter (not . null) (map (ppFormulaInst unicode formBindings termBindings) sucs))

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
ppCalculus unicode (Calculus name axioms rules) =
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

-- | Pretty print a 'GoalSpec'.
ppGoalSpec :: GoalSpec -> String
ppGoalSpec [] = "top"
ppGoalSpec gs = intercalate "." (map show gs)

-- | \"Pretty\" print a derivation.
ppDerivation :: Bool -> Derivation -> String
ppDerivation unicode = ppDerivation' unicode "" [] where
  ppDerivation' unicode pad spec (Stub conclusion) =
    pad ++ ppSequent unicode conclusion ++ " (unproved) [" ++ ppGoalSpec spec ++ "]\n"
  ppDerivation' unicode pad spec (Axiom conclusion axiom _ _) =
    pad ++ ppSequent unicode conclusion ++ " (by " ++ axiom ++ ") [" ++ ppGoalSpec spec ++ "]\n"
  ppDerivation' unicode pad spec (Der conclusion rule _ _ premises) =
    pad ++ ppSequent unicode conclusion ++ " (by " ++ rule ++ ") [" ++ ppGoalSpec spec ++ "]\n" ++
    (concat $ ppPremises spec 1 premises)
    where ppPremises spec n [] = []
          ppPremises spec n (prem:prems) =
            ppDerivation' unicode (pad++"  ") (spec ++ [n]) prem : ppPremises spec (n+1) prems

-- Pretty printing a derivation
-- TODO: put an asterisk at the current subgoal
-- TODO: maybe move some of these printing functions to a separate file (Main?)
ppDerivationTree' :: Bool -> GoalSpec -> Derivation -> GoalSpec -> String
ppDerivationTree' unicode subgoal (Stub conclusion) spec =
  ppSequent unicode conclusion ++ if spec == subgoal then "*\n" else "\n"
ppDerivationTree' unicode subgoal (Axiom conclusion axiom _ _) spec =
  "[" ++ ppSequent unicode conclusion ++ "]" ++ if spec == subgoal then "*\n" else "\n"
ppDerivationTree' unicode subgoal (Der conclusion rule _ _ ders) spec =
  let newSpecs = zipWith (++) (repeat spec) (map (:[]) [1..length ders])
      ppDers = zipWith (ppDerivationTree' unicode subgoal) ders newSpecs
      premString = foldl spliceStrings "" ppDers
      premStringWidth = case premString of (_:_) -> maximum (map length (lines premString))
                                           _     -> 0
      concString = ppSequent unicode conclusion ++ if spec == subgoal then "*" else ""
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
ppDerivationTree :: Bool -> Derivation -> GoalSpec -> String
ppDerivationTree unicode der subgoal = ppDerivationTree' unicode subgoal der []
