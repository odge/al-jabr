module Concrete.Integer (Integer) where

import Technology.Labels
import Abstract.Magma
import Abstract.Semigroup
import Abstract.Abelian
import Abstract.Monoid
import Abstract.Group
import Abstract.Ring

import qualified Prelude as P

type Integer = P.Integer

instance Magma Integer Additive where getBinaryOperation _ = (P.+)
instance Magma Integer Multiplicative where getBinaryOperation _ = (P.*)
instance Semigroup Integer Additive where
instance Semigroup Integer Multiplicative where
instance Abelian Integer Additive where
instance Abelian Integer Multiplicative where
instance Monoid Integer Additive where getIdentity _ = 0
instance Monoid Integer Multiplicative where getIdentity _ = 1
instance Group Integer Additive where getInverse _ = P.negate
instance Ring Integer Additive Multiplicative where
