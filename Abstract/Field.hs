module Abstract.Field (Nonzero(..), Field(..)) where

import Abstract.Group
import Abstract.Ring

type Nonzero a = a

class (Ring m id id', Group (Nonzero m) id') => Field m id id' where
-- 0 /= 1
