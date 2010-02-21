module Abstract.Ring (Ring(..)) where

import Abstract.Abelian
import Abstract.Group
import Abstract.Monoid

class (Abelian m id, Group m id, Monoid m id') => Ring m id id' where
-- (a+b)c = ac+bc
-- c(a+b) = ca+cb
