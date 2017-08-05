module Parse where

import Calculus

import Control.Applicative hiding (many)
import Control.Applicative.Alternative
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

many :: Parser a -> Parser [a]
many p = many1 p <|> return []

many1 :: Parser a -> Parser [a]
many1 p = do { a <- p; as <- many p; return (a:as) }

sepBy :: Parser sep -> Parser a -> Parser [a]
sepBy sep p = sepBy1 sep p <|> return []

sepBy1 :: Parser sep -> Parser a -> Parser [a]
sepBy1 sep p = do a <- p
                  as <- many (do { sep; p })
                  return (a:as)

between l r p = l *> p <* r

(<||>) :: Parser a -> Parser a -> Parser a
p <||> q = Parser (\cs -> case parse (p <|> q) cs of
                      (x:_) -> [x]
                      _     -> [])

--------------------------------------------------------------------------------
-- Concretes

item :: Parser Char
item = Parser (\cs -> case cs of
                  (c:cs') -> [(c,cs')]
                  _       -> [])

items :: Parser String
items = many item

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
-- Terms

term :: Parser Term
term = (constTerm <|> varTerm <|> appTerm)

constTerm :: Parser Term
constTerm = do char '_'
               name <- many1 alphaNum
               return $ ConstTerm name

varTerm :: Parser Term
varTerm = do name <- many1 alphaNum
             return $ VarTerm name

termList :: Parser [Term]
termList = sepBy (spaces *> char ',' *> spaces) term

appTerm :: Parser Term
appTerm = do name <- many1 alphaNum
             subTerms <- paren termList
             return $ AppTerm name subTerms

--------------------------------------------------------------------------------
-- Formulas

-- TODO: add forall a b c. A(a,b,c)
-- TODO: finish parsing

formula :: Calculus -> Parser Formula
formula = undefined -- opFormula <|> baseFormula

opFormula :: UniName -> Parser Formula
opFormula (aop, uop) = do a <- baseFormula
                          spaces
                          (string aop <|> string uop)
                          spaces
                          sf <- formula
                          return $ Op (aop, uop) a sf

baseFormula :: Parser Formula
baseFormula = paren formula <|>
              terminalFormula <|>
              quantFormula

terminalFormula :: Parser Formula
terminalFormula = predFormula <|> bottomFormula

forallFormula :: Parser Formula
forallFormula = do string "forall"
                   char ' '
                   spaces
                   x <- many1 alphaNum
                   spaces
                   char '.'
                   spaces
                   bf <- baseFormula
                   return $ Forall x bf

predFormula :: Parser Formula
predFormula = atomFormula <|> predAppFormula

atomFormula :: Parser Formula
atomFormula = do { name <- many1 alphaNum; return $ Pred name [] }

predAppFormula :: Parser Formula
predAppFormula = do name <- many1 alphaNum
                    terms <- paren termList
                    return $ Pred name terms

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
