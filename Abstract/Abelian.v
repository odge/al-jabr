Require Import
  Technology.FirstClassSetoid
  Technology.Tag
  Abstract.Magma.

Set Automatic Introduction.

Delimit Scope algebra_scope with algebra.
Open Scope algebra_scope.

Class Abelian `(M : Magma) := {
  commutativity : forall a b,
    a & b == b & a
}.
