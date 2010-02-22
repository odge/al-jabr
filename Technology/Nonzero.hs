module Nonzero (Nonzero(..)) where

newtype Nonzero a = Nonzero { unNonzero :: a }

instance Show a => Show (Nonzero a) where show (Nonzero x) = show x
