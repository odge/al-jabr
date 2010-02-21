module Concrete.Natural (Natural) where

import Technology.Bottom
import Technology.Labels
import Abstract.Magma
import Abstract.Semigroup
import Abstract.Abelian
import Abstract.Monoid
import Abstract.Group
import Abstract.Ring
import Concrete.Integer

import Prelude (($))

newtype Natural = Natural Integer

instance Magma Natural Additive where
 getBinaryOperation _ (Natural i) (Natural j) = Natural $ getBinaryOperation (__ :: Additive) i j
instance Magma Natural Multiplicative where
 getBinaryOperation _ (Natural i) (Natural j) = Natural $ getBinaryOperation (__ :: Multiplicative) i j
instance Semigroup Natural Additive where
instance Semigroup Natural Multiplicative where
instance Abelian Natural Additive where
instance Abelian Natural Multiplicative where
instance Monoid Natural Additive where getIdentity _ = Natural 0
instance Monoid Natural Multiplicative where getIdentity _ = Natural 1
