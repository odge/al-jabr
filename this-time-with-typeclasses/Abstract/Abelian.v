Require Import
  Technology.Setoid
  Abstract.Magma.

Class Abelian `(m : Magma) := {
  commutativity : forall a b, a&b == b&a
}.
