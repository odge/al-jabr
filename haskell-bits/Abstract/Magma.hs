module Abstract.Magma (Magma(..)) where

class Magma m id where getBinaryOperation :: id -> m -> m -> m
