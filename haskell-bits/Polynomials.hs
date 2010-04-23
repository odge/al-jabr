module Polynomials
 ( Monomial(..), Polynomial(..)
 , evalMonomial, evalPolynomial
 , polynomialFromConstant
 , polynomialFromVariable
 ) where

import Prelude hiding ((+),(-),(*),(/),Rational(..))
import qualified Prelude as P
import Data.List
import qualified Data.Map as M

import Operations
import Numbers

type i :--> k = M.Map i k

newtype Monomial v = Monomial (v :--> Natural) deriving (Eq, Ord)
newtype Polynomial v c = Polynomial (Monomial v :--> c) deriving (Eq, Ord)

evalMonomial (^) evalVariable (Monomial m) = product (map (\(v,i) -> evalVariable v ^ i) (M.toList m))
 where product = foldl (*) one
evalPolynomial (^) evalV (Polynomial p) = sum (map (\(m,c) -> c * evalMonomial (^) evalV m) (M.toList p))
 where sum = foldl (+) zero

polynomialFromConstant c = Polynomial (M.fromList [(one, c)])
polynomialFromVariable v = Polynomial (M.fromList [(Monomial (M.fromList [(v,one)]), one)])

instance (Ord v, Add c) => Add (Polynomial v c) where
 zero = Polynomial (M.fromList [])
 Polynomial p + Polynomial q = Polynomial (M.unionWith (+) p q)

instance                (Ord v) => Mul (Monomial v) where
 one = Monomial (M.fromList [])
 Monomial m * Monomial n = Monomial (M.unionWith (+) m n)
instance  (Ord v, Add c, Mul c) => Mul (Polynomial v c) where
 one = Polynomial (M.fromList [(one, one)])
 Polynomial p * Polynomial q = Polynomial . M.fromListWith (+) $
  do (m, a) <- M.toList p
     (n, b) <- M.toList q
     return (m * n, a * b)

------------------------------------------------------------------------------
-- just for debugging

instance           Show v => Show (Monomial v) where
 show (Monomial m) =
  concatMap (\v -> show (fst v) ++ "^" ++ show (snd v)) (M.toList m)
instance (Show v, Show c) => Show (Polynomial v c) where
 show (Polynomial p) =
  intercalate " + " (map (\m -> show (snd m) ++ show (fst m)) (M.toList p))
