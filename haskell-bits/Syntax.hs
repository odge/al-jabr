module Syntax
 ( Term(..), Syntax(..), term
 , Algebraic(..)
 ) where

import Prelude hiding ((+),(-),(*),(/))
import qualified Prelude as P
import Text.ParserCombinators.Parsec hiding (space)
import Text.ParserCombinators.Parsec.Expr

import Operations (zero,one)
import qualified Operations as O

space = showString " "

data Term op = A String | O (Maybe op) (Term op) (Term op)

class Syntax op where
 limit :: op -> Int
 level :: op -> Int
 symbol :: op -> String
 associativity :: op -> Assoc
 table :: OperatorTable Char st (Term op)

instance Syntax op => Show (Term op) where
 showsPrec d (A v) = showString v
 showsPrec d (O Nothing f x) = showParen (d > limit o) $
  showsPrec (limit o) f . space . showsPrec (limit o P.+ 1) x where
   o = (undefined :: Term op -> op) f
 showsPrec d (O (Just o) a b) = showParen (d > level o) $
  showsPrec (level o P.+ l) a . space . showString (symbol o) . space . showsPrec (level o P.+ r) b where
   (l, r) = case associativity o of AssocLeft -> (0, 1) ; AssocRight -> (1, 0) ; AssocNone -> (1, 1)

term = do spaces ; t <- term' ; eof ; return t where
 term' = buildExpressionParser (functionApplication : table) expr
 expr = atom <|> parens term'
 atom = (do name <- many1 alphaNum ; spaces ; return (A name)) <?> "atom"
 functionApplication = [ Infix (do spaces ; return (O Nothing)) AssocLeft ]
 parens p = do char '(' ; spaces ; x <- p ; char ')' ; spaces ; return x

data Algebraic = Add | Sub | Mul | Div | Pow deriving Show
instance Syntax Algebraic where
 limit _ = 5
 level Pow = 3
 level Mul = 2
 level Div = 2
 level Sub = 1
 level Add = 1
 symbol Pow = "^"
 symbol Mul = "*"
 symbol Div = "/"
 symbol Sub = "-"
 symbol Add = "+"
 associativity Pow = AssocRight
 associativity Mul = AssocLeft
 associativity Div = AssocLeft
 associativity Add = AssocLeft
 associativity Sub = AssocLeft
 table =
  [[ Infix (do string "^" ; spaces ; return (O (Just Pow))) AssocRight ]
  ,[ Infix (do string "*" ; spaces ; return (O (Just Mul))) AssocLeft
   , Infix (do string "/" ; spaces ; return (O (Just Div))) AssocLeft ]
  ,[ Infix (do string "+" ; spaces ; return (O (Just Add))) AssocLeft
   , Infix (do string "-" ; spaces ; return (O (Just Sub))) AssocLeft ] ]

instance O.Add (Term Algebraic) where
 zero = A "0" ; (+) = O (Just Add) -- not commutative!
instance O.Sub (Term Algebraic) where
 neg = O (Just Sub) zero
instance O.Mul (Term Algebraic) where
 one = A "1" ; (*) = O (Just Mul)
instance O.Div (Term Algebraic) where
 inv = O (Just Div) one
