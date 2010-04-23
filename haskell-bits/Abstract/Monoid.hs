module Abstract.Monoid (Monoid(..)) where

import Abstract.Semigroup

class Semigroup m id => Monoid m id where
 getIdentity :: id -> m
-- ea = a = ae

