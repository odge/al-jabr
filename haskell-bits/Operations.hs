module Operations
 ( Add(..), Sub(..), (-), Mul(..), Div(..), (/)
 , GCD(..), UFD(..)
 ) where

import Prelude hiding ((+),(-),(*),(/))

infixl 6 +
infixl 6 -
infixl 7 *
infixl 7 /

class Add a where
 zero :: a
 (+) :: a -> a -> a
class Sub a where
 neg :: a -> a
(-) :: (Add a, Sub a) => a -> a -> a
x - y = x + neg y
class Mul a where
 one :: a
 (*) :: a -> a -> a
class Div a where
 inv :: a -> a
(/) :: (Mul a, Div a) => a -> a -> a
x / y = x * inv y

class GCD a where
 gcd :: a -> a -> a
class UFD a where
 factorize :: a -> Maybe [(a, Int)]
