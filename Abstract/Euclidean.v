Require Import
  Technology.FirstClassSetoid
  Technology.Tag
  Abstract.Magma
  Abstract.Semigroup
  Abstract.Monoid
  Abstract.Group
  Abstract.Ring
  Abstract.Integral
  Concrete.N.

Set Automatic Introduction.

Delimit Scope algebra_scope with algebra.
Open Scope algebra_scope.

Class Euclidean S `(I : Integral S) := {
  degreeFunction : S -> N ;
  degreeFunctionRespectful : Proper (eq S ==> eq N) degreeFunction
}.
