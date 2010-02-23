Require Import
  Technology.Setoid
  Abstract.Magma.

Class Semigroup `(m : Magma) := {
  associativity : forall a b c, (a&b)&c == a&(b&c)
}.
