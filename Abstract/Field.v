Require Import
  Technology.FirstClassSetoid
  Technology.Tag
  Abstract.Magma
  Abstract.Monoid
  Abstract.Abelian
  Abstract.Ring.

Set Automatic Introduction.

Delimit Scope algebra_scope with algebra.
Open Scope algebra_scope.

Class Field S `(R : Ring S) `(AddAbl : @Abelian _ _ Add) `(MulAbl : @Abelian _ _ Mul) := {
  nonDegernerate' : one # zero ;
  reciprocal : forall a, a # zero -> S ;
  reciprocalLeftInverse : forall a (prf : a # zero),
    reciprocal a prf * a == one ;
  reciprocalRightInverse : forall a (prf : a # zero),
    a * reciprocal a prf == one
}.
