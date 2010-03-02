Require Import
  Technology.FirstClassSetoid
  Technology.Tag
  Abstract.Magma.

Set Automatic Introduction.

Delimit Scope algebra_scope with algebra.
Open Scope algebra_scope.

Class Semigroup `(M : Magma) := {
  associativity : forall a b c,
    a & (b & c) == (a & b) & c
}.
