Require Import
 Technology.Setoid.

Section Magma.

Variable S : Setoid.
Variable operation : car S -> car S -> car S.

Class Magma
  : Prop := {
    operationRespectful : Proper (eq S ==> eq S ==> eq S) operation
  }.

Add Parametric Morphism (Mag : Magma) : operation with 
signature eq S ==> eq S ==> eq S as operation_mor.
Proof. apply operationRespectful. Qed.

End Magma.


Section Abelian_and_Semigroup.

Variable S : Setoid.
Variable operation : car S -> car S -> car S.
Variable Mag : Magma S operation.

Infix "&" := operation (at level 20).

Class Abelian
  : Prop := {
    commutative : forall x y, x & y == y & x
  }.

Class Semigroup
  : Prop := {
    associative : forall x y z, (x & y) & z == x & (y & z)
  }.

End Abelian_and_Semigroup.


Section Monoid_and_Group.

Variable S : Setoid.
Variable operation : car S -> car S -> car S.
Variable Mag : Magma S operation.
Variable Sem : Semigroup S operation.
Variable e : car S.

Infix "&" := operation (at level 20).

Class Monoid
  : Prop := {
    leftIdentity : forall x, e & x == x ;
    rightIdentity : forall x, x & e == x
  }.

Variable inverse : car S -> car S.

Class Group
  : Prop := {
    inverseRespectful : Proper (eq S ==> eq S) inverse ;
    leftInverse : forall x, inverse x & x == e ;
    rightInverse : forall x, x & inverse x == e
  }.

Add Parametric Morphism (Grp : Group) : inverse with 
signature eq S ==> eq S as inverse_mor.
Proof. apply inverseRespectful. Qed.

End Monoid_and_Group.



Section Ring_and_Integral.

Variable S : Setoid.

Variable add : car S -> car S -> car S.
Variable mul : car S -> car S -> car S.
Variable zero : car S.
Variable one : car S.
Variable neg : car S -> car S.

Variable MagA : Magma S add.
Variable AblA : Abelian S add.
Variable SemA : Semigroup S add.
Variable MonA : Monoid S add zero.
Variable GrpA : Group S add zero neg.
Variable MagM : Magma S mul.
Variable SemM : Semigroup S mul.
Variable MonM : Monoid S mul one.

Infix "(+)" := add (at level 50).
Notation "p '(x)' q" := (mul p q) (at level 40).

Class Ring
  : Prop := {
    leftDistributivity : forall k x y, k (x) (x (+) y) == k (x) x (+) k (x) y ;
    rightDistributivity : forall k x y, (x (+) y) (x) k == x (x) k (+) y (x) k
  }.

Class Integral
  : Prop := {
    nondegenerate : zero # one ;
    noZeroDivisors : forall p q, p (x) q == zero -> p == zero \/ q == zero
  }.

Theorem left_cancellation : forall k x y,
  k # zero -> k (x) x == k (x) y -> x == y.
Proof.
  intros k x y; intros k_ap_zero eq0.

assert (k (x) neg y == neg (k (x) y)).
assert (k (x) neg y (+) k (x) y == neg (k (x) y) (+) k (x) y).
rewrite leftInverse.
(** this is bad because you have to write out the group name ***)

Admitted.

End Ring_and_Integral.
