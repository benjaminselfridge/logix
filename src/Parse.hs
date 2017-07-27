{-# LANGUAGE ScopedTypeVariables #-}

module Parse where

import Calculus

import Control.Applicative hiding (many)
import Control.Monad
import Data.Char (isDigit, isAlpha)
import Data.List

newtype Parser a = Parser { parse :: String -> [(a,String)] }

instance Functor Parser where
  fmap f (Parser p) = Parser (\cs -> [ (f a, cs') | (a, cs') <- p cs])

instance Applicative Parser where
  pure x = Parser (\cs -> [(x, cs)])
  (Parser p) <*> (Parser q) = Parser r where
    r s = [ (f a, u) | (f, t) <- p s
                     , (a, u) <- q t]

instance Monad Parser where
  return = pure

  p >>= f = Parser (\cs -> [ (b, cs'') | (a, cs')  <- parse p cs
                                       , (b, cs'') <- parse (f a) cs'])

-- Are these instances valid?
instance Alternative Parser where
  empty = Parser (\_ -> [])
  p <|> q = Parser (\cs -> [ (a, cs') | (a, cs') <- parse p cs ] ++
                           [ (a, cs') | (a, cs') <- parse q cs ])

instance MonadPlus Parser where
  mzero = empty
  mplus = (<|>)

--------------------------------------------------------------------------------
-- combinators

-- TODO: remove shows

many :: Parser a -> Parser [a]
-- many p = Parser ps where
--   ps cs = case parse p cs of
--             [] -> [([], cs)]
--             [(a,cs')] -> map (\(as, leftover) -> (a:as, leftover)) $ parse (many p) cs'
many p = many1 p <|> return []

many1 :: Parser a -> Parser [a]
-- many1 p = do
--   a  <- p
--   as <- many p
--   return (a:as)
many1 p = do { a <- p; as <- many p; return (a:as) }

between l r p = l *> p <* r

sepBy :: Parser sep -> Parser a -> Parser [a]
-- sepBy sep p = Parser ps where
--   ps cs = case parse p cs of
--             [] -> [([], cs)]
--             [(a,cs')] -> map (\(as, leftover) ->
--                                 (a:as, leftover)) $ parse (many (sep >> p)) cs'
sepBy sep p = sepBy1 sep p <|> return []

sepBy1 :: Parser sep -> Parser a -> Parser [a]
sepBy1 sep p = do a <- p
                  as <- many (do { sep; p })
                  return (a:as)

--------------------------------------------------------------------------------
-- Concretes

char :: Char -> Parser Char
char c = Parser (\cs -> case cs of
                    (c':cs') | c == c' -> [(c,cs')]
                    _                  -> [])
  
string :: String -> Parser String
string s = Parser (\cs -> case stripPrefix s cs of
                      Just cs' -> [(s, cs')]
                      _        -> [])

digit :: Parser Char
digit = Parser (\cs -> case cs of
                   (c':cs') | isDigit c' -> [(c',cs')]
                   _                     -> [])

int :: Parser Int
int = do digits <- many1 digit
         return $ read digits

alpha :: Parser Char
alpha = Parser (\cs -> case cs of
                   (c':cs') | isAlpha c' -> [(c',cs')]
                   _                     -> [])

alphaNum :: Parser Char
alphaNum = alpha <|> digit

space   = do { char ' ' ; return () }
tab     = do { char '\t'; return () }
newline = do { char '\n'; return () }

spaces = do { many (space <|> tab); return () }

lpar = char '('
rpar = char ')'

paren = between lpar rpar

end :: Parser ()
end = Parser (\cs -> case cs of
                 [] -> [((), "")]
                 _  -> [])

--------------------------------------------------------------------------------
-- Formulas

-- TODO: add <->

topFormula :: Parser Formula
topFormula = spaces *> formula <* spaces <* end

formula :: Parser Formula
-- formula = (implFormula <|> subFormula)
formula = (iffFormula <|> implSubFormula)

iffFormula :: Parser Formula
iffFormula = do impf <- implSubFormula
                spaces
                string "<->"
                spaces
                f <- formula
                return $ And (Implies impf f) (Implies f impf)

implSubFormula :: Parser Formula
implSubFormula = implFormula <|> subFormula

implFormula :: Parser Formula
implFormula = do sf <- subFormula
                 spaces
                 string "->"
                 spaces
                 f <- formula
                 return $ Implies sf f

subFormula :: Parser Formula
subFormula = andFormula <|>
             orFormula <|>
             baseFormula

andFormula :: Parser Formula
andFormula = do a <- baseFormula
                spaces
                char '&'
                spaces
                sf <- subFormula
                return $ And a sf

orFormula :: Parser Formula
orFormula = do a <- baseFormula
               spaces
               char '|'
               spaces
               sf <- subFormula
               return $ Or a sf

baseFormula :: Parser Formula
baseFormula = paren formula <|> terminalFormula <|> negFormula

terminalFormula :: Parser Formula
terminalFormula = atomFormula <|> bottomFormula

negFormula :: Parser Formula
negFormula = do char '~'
                spaces
                bf <- baseFormula
                return $ Implies bf Bottom

atomFormula :: Parser Formula
atomFormula = do { name <- many1 alphaNum; return $ Atom name }

bottomFormula :: Parser Formula
bottomFormula = do { string "_|_"; return Bottom }

--------------------------------------------------------------------------------
-- Sequents

formulaList :: Parser [Formula]
formulaList = sepBy (spaces *> char ',' *> spaces) formula

sequent :: Parser Sequent
sequent = do ants <- formulaList
             spaces
             string "=>"
             spaces
             sucs <- formulaList
             return $ ants :=> sucs

--------------------------------------------------------------------------------
-- Top-level parser

parseSequent :: String -> [(Sequent, String)]
parseSequent = parse $ spaces *> sequent <* spaces