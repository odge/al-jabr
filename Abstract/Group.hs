module Abstract.Group (Group(..)) where

import Abstract.Monoid

class Monoid m id => Group m id where
 getInverse :: id -> m -> m
-- aa' = e = a'a

