Require Import
  Technology.FirstClassSetoid.

Set Automatic Introduction.

Delimit Scope algebra_scope with algebra.
Open Scope algebra_scope.

Inductive Tag : Set := Additive | Multiplicative.

Class Magma (tag : Tag) (S : Setoid) := {
  operation : S -> S -> S ;
  operationRespectful : Proper (eq S ==> eq S ==> eq S) operation
}.

Infix "&" := operation (at level 50, no associativity) : algebra_scope.
Infix "(+)" := (@operation Additive _ _) (at level 50, no associativity) : algebra_scope.
Infix "(x)" := (@operation Multiplicative _ _) (at level 40, no associativity) : algebra_scope.

Add Parametric Morphism (tag : Tag) (S : Setoid) `(m : Magma tag S) : operation with 
signature eq S ==> eq S ==> eq S as operation_mor.
Proof. apply operationRespectful. Qed.

(** tests **

Lemma magma_morph_test `{m : Magma} : forall x y a,
  x == y -> a&x == a&y.
intros tag M m x y a Q.
rewrite Q; reflexivity.
Qed.

Lemma magma_ops_test (S : Setoid) `(A : Magma Additive S) (B : Magma Multiplicative S) :
  forall a b c,
    a (+) b (x) c ==
    @operation Additive _ _ a (@operation Multiplicative _ _ b c).
reflexivity.
Qed.

** **)

Class Semigroup `(M : Magma) := {
  associativity : forall a b c,
    a & (b & c) == (a & b) & c
}.

Class Abelian `(M : Magma) := {
  commutativity : forall a b,
    a & b == b & a
}.

Class Monoid `(M : Magma) := {
  identity ;
  leftIdentity : forall x, identity & x == x ;
  rightIdentity : forall x, x & identity == x
}.

Notation "'zero'" := (@identity Additive _ _ _) : algebra_scope.
Notation "'one'" := (@identity Multiplicative _ _ _) : algebra_scope.

(** tests **

Theorem monoid_test (S : Setoid) `(A : Monoid Additive S) `(M : Monoid Multiplicative S) :
  zero (x) one == zero (+) zero.
intros.
rewrite leftIdentity.
rewrite rightIdentity.
reflexivity.
Qed.

** **)

Class Group (tag : Tag) (S : Setoid) `(M : Magma tag S) `(Sem : @Semigroup tag S M) `(Mo : @Monoid tag S M) := {
  invert : S -> S ;
  invertRespectful : Proper (eq S ==> eq S) invert ;
  leftInverse : forall x, invert x & x == identity ;
  rightInverse : forall x, x & invert x == identity
}.

Notation "x '''" := (@invert _ _ _ _ _ _ x) (at level 40, no associativity) : algebra_scope.

Add Parametric Morphism (tag : Tag) (S : Setoid) `(m : Group tag S) : invert with 
signature eq S ==> eq S as invert_mor.
Proof. apply invertRespectful. Qed.

Ltac Group_intros Name := intros tag S M Sem Mo Name.

(** tests

Theorem group_test `(G : Group) :
  forall x,
    x & x ' == identity.
intros.
rewrite rightInverse.
reflexivity.
Qed.

**)

Class Ring (S : Setoid) `(Add : Magma Additive S) `(Mul : Magma Multiplicative S)
  (AddSem : @Semigroup _ _ Add) (MulSem : @Semigroup _ _ Mul)
  (AddMon : @Monoid _ _ Add) (MulMon : @Monoid _ _ Mul)
  (AddGrp : @Group _ _ Add AddSem AddMon) := {
  leftDistributivity : forall k a b,
    k (x) (a (+) b) == (k (x) a) (+) (k (x) b) ;
  rightDistributivity : forall k a b,
    (a (+) b) (x) k == (a (x) k) (+) (b (x) k)
}.

Class Integral `(R : Ring) := {
  nonDegernerate : one # zero ;
  noZeroDivisors : forall a b,
    a (x) b == zero -> a == zero \/ b == zero
}.
