module Parse where

import Calculus

import Control.Applicative hiding (many)
import Control.Applicative.Alternative hiding (many)
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
formula calc = asum (map (\op -> opFormula calc op) (calcBinaryOps calc)) <|> baseFormula calc

opFormula :: Calculus -> UniName -> Parser Formula
opFormula calc op@(UniName (aop, uop)) = do
  a <- baseFormula calc
  spaces
  string aop <|> string uop
  spaces
  sf <- formula calc
  return $ BinaryOp op a sf

baseFormula :: Calculus -> Parser Formula
baseFormula calc = paren (formula calc) <|>
                   terminalFormula calc <|>
                   asum (map (\qt -> quantFormula calc qt) (calcQts calc))

terminalFormula :: Calculus -> Parser Formula
terminalFormula calc = predFormula <|>
                       asum (map (\op -> zeroaryFormula op) (calcZeroaryOps calc))

quantFormula :: Calculus -> UniName -> Parser Formula
quantFormula calc qt@(UniName (aqt, uqt)) = do
  string aqt <|> string uqt
  spaces
  x <- many1 alphaNum
  spaces
  char '.'
  spaces
  bf <- baseFormula calc
  return $ Quant qt x bf

predFormula :: Parser Formula
predFormula = predAppFormula <|> atomFormula

atomFormula :: Parser Formula
atomFormula = do { name <- many1 alphaNum; return $ Pred name [] }

predAppFormula :: Parser Formula
predAppFormula = do name <- many1 alphaNum
                    terms <- paren termList
                    return $ Pred name terms

zeroaryFormula :: UniName -> Parser Formula
zeroaryFormula op@(UniName (aqt, uqt))  = do
  string aqt <|> string uqt
  return $ ZeroaryOp op

--------------------------------------------------------------------------------
-- Sequents

formulaList :: Calculus -> Parser [Formula]
formulaList calc = sepBy (spaces *> char ',' *> spaces) (formula calc)

sequent :: Calculus -> Parser Sequent
sequent calc = do ants <- formulaList calc
                  spaces
                  string "=>"
                  spaces
                  sucs <- formulaList calc
                  return $ ants :=> sucs
