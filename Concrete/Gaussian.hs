module Concrete.Gaussian (Gaussian(..)) where

import Technology.Bottom
import Technology.Labels
import Abstract.Magma
import Abstract.Semigroup
import Abstract.Abelian
import Abstract.Monoid
import Abstract.Group
import Abstract.Ring

data Gaussian m = m :+: m

instance Magma a Additive => Magma (Gaussian a) Additive where
 getBinaryOperation _ (x :+: y) (u :+: v) = (x + u) :+: (y + v)
  where (+) = getBinaryOperation (__ :: Additive)
instance (Group a Additive, Magma a Multiplicative) => Magma (Gaussian a) Multiplicative where
 getBinaryOperation _ (x :+: y) (u :+: v) = (x * u + negate (y * v)) :+: ((x * v) + (y * u))
  where (+) = getBinaryOperation (__ :: Additive)
        negate = getInverse (__ :: Additive)
        (*) = getBinaryOperation (__ :: Multiplicative)
