module Abstract.Field (Nonzero(..), Field(..)) where

import Technology.Nonzero
import Abstract.Group
import Abstract.Ring

class (Ring m id id', Group (Nonzero m) id') => Field m id id' where
-- 0 /= 1
