module Abstract.Abelian (Abelian(..)) where

import Abstract.Magma

class Magma m id => Abelian m id where
-- ab = ba
