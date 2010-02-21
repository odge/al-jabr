module Abstract.Semigroup (Semigroup(..)) where

import Abstract.Magma

class Magma m id => Semigroup m id where
-- (ab)c = abc = a(bc)

