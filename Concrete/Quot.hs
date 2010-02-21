module Concrete.Quot (Quot(..)) where

import Technology.Bottom
import Technology.Labels
import Abstract.Magma
import Abstract.Semigroup
import Abstract.Abelian
import Abstract.Monoid
import Abstract.Group
import Abstract.Ring
import Abstract.Field

data Quot m = m :/: m

instance Magma a Multiplicative => Magma (Quot a) Multiplicative where
 getBinaryOperation _ (x :/: y) (u :/: v) = (x * u) :/: (y * v)
  where (*) = getBinaryOperation (__ :: Multiplicative)
instance (Magma a Additive, Magma a Multiplicative) => Magma (Quot a) Additive where
 getBinaryOperation _ (x :/: y) (u :/: v) = ((x * v) + (u * y)) :/: (y * v)
  where (+) = getBinaryOperation (__ :: Additive)
        (*) = getBinaryOperation (__ :: Multiplicative)
