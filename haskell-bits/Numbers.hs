module Numbers
 ( Natural(..), Rational(..), Complex(..)
 ) where

import Prelude hiding ((+),(-),(*),(/),Rational(..),gcd)
import qualified Prelude as P

import Primes

import Operations

newtype Natural = Natural Integer deriving (Ord)
data Rational a = a :/: a
data Complex a = a :+: a

instance                                 Show Natural where
 show (Natural n) = show n
instance (Show a, Eq a, Mul a)        => Show (Rational a) where
 show (x :/: o) | o == one = show x
 show (x :/: y)            = show x ++ "/" ++ show y
instance (Show a, Eq a, Add a, Mul a) => Show (Complex a) where
 show (x :+: z) | z == zero             = show x
 show (z :+: o) | z == zero && o == one = "i"
 show (z :+: y) | z == zero             = "i*" ++ show y
 show (x :+: y)                         = show x ++ "+i*" ++ show y

instance                  Eq Natural where
 Natural x == Natural y = x == y
instance (Eq a, Mul a) => Eq (Rational a) where
 x :/: y == u :/: v = x * v == u * y
instance          Eq a => Eq (Complex a) where
 x :+: y == u :+: v = x == u && y == v

instance                   Add Integer where
 zero = 0
 x + y = x P.+ y
instance                   Add Natural where
 zero = Natural zero
 Natural x + Natural y = Natural (x + y)
instance (Add a, Mul a) => Add (Rational a) where
 zero = zero :/: one
 x :/: y + u :/: v = (x * v + u * y) :/: (y * v)
instance          Add a => Add (Complex a) where
 zero = zero :+: zero
 x :+: y + u :+: v = (x + u) :+: (y + v)

instance          Sub Integer where
 neg x = P.negate x
instance Sub a => Sub (Rational a) where
 neg (x :/: y) = (neg x) :/: y
instance Sub a => Sub (Complex a) where
 neg (x :+: y) = neg x :+: neg y

instance                          Mul Integer where
 one = 1
 x * y = x P.* y
instance                          Mul Natural where
 one = Natural one
 Natural x * Natural y = Natural (x * y)
instance                 Mul a => Mul (Rational a) where
 one = one :/: one
 x :/: y * u :/: v = (x * u) :/: (y * v)
instance (Add a, Sub a, Mul a) => Mul (Complex a) where
 one = one :+: zero
 x :+: y * u :+: v = (x * u - y * v) :+: (x * v + y * u)

instance                                 Div (Rational a) where
 inv (x :/: y) = y :/: x
instance (Add a, Sub a, Mul a, Div a) => Div (Complex a) where
 inv (x :+: y) = (x / r) :+: neg (y / r) where r = x * x + y * y

instance GCD Natural where
 gcd (Natural x) (Natural y) = Natural (P.gcd x y)
instance GCD Integer where
 gcd = P.gcd

instance UFD Natural where
 factorize (Natural 0) = Nothing
 factorize (Natural i) = Just $ (map (\(x,y) -> (Natural x, y)) (primePowerFactors i))
instance UFD Integer where
 factorize i | i < 0 = Just $ (-1,1) : primePowerFactors (neg i)
 factorize i | i == 0 = Nothing
 factorize i | i > 0 = Just $ primePowerFactors i
