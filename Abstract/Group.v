Require Import
  Technology.FirstClassSetoid
  Technology.Tag
  Abstract.Magma
  Abstract.Semigroup
  Abstract.Monoid.

Set Automatic Introduction.

Delimit Scope algebra_scope with algebra.
Open Scope algebra_scope.

Class Group (tag : Tag) (S : Setoid) `(M : Magma tag S) `(Sem : @Semigroup tag S M) `(Mo : @Monoid tag S M) := {
  invert : S -> S ;
  invertRespectful : Proper (eq S ==> eq S) invert ;
  leftInverse : forall x, invert x & x == identity ;
  rightInverse : forall x, x & invert x == identity
}.

Notation "x '''" := (@invert _ _ _ _ _ _ x) (at level 30, no associativity) : algebra_scope.

Add Parametric Morphism (tag : Tag) (S : Setoid) `(m : Group tag S) : invert with 
signature eq S ==> eq S as invert_mor.
Proof. apply invertRespectful. Qed.

Lemma group_identity_self_inverse `(G : Group) :
  identity ' == identity.
Proof.
  assert (identity ' & identity == identity) as Q by (rewrite leftInverse; reflexivity).
  rewrite rightIdentity in Q.
  assumption.
Qed.

Lemma group_unique_identity_left `(G : Group) : forall x y,
  x & y == y -> x == identity.
Proof.
  intros x y Q. 
  assert ((x & y) & y ' == y & y ') as Q' by (rewrite Q; reflexivity).
  rewrite <- associativity in Q'.
  repeat rewrite rightInverse in Q'.
  rewrite rightIdentity in Q'.
  assumption.
Qed.

Lemma group_unique_identity_right `(G : Group) : forall x y,
  y & x == y -> x == identity.
Proof.
  intros x y Q. 
  assert (y ' & (y & x) == y ' & y) as Q' by (rewrite Q; reflexivity).
  rewrite associativity in Q'.
  repeat rewrite leftInverse in Q'.
  rewrite leftIdentity in Q'.
  assumption.
Qed.

Lemma group_unique_inverses `(G : Group) : forall x y,
  x & y == identity -> x == y ' /\ y == x '.
Proof.
  intros x y Q.
  assert ((x & y) & y ' == identity & y ') as Qa by (rewrite Q; reflexivity).
  assert (x ' & (x & y) == x ' & identity) as Qb by (rewrite Q; reflexivity).
  rewrite <- associativity in Qa.
  rewrite associativity in Qb.
  rewrite rightInverse in Qa.
  rewrite leftInverse in Qb.
  rewrite leftIdentity in Qa.
  rewrite rightIdentity in Qa.
  rewrite rightIdentity in Qb.
  rewrite leftIdentity in Qb.
  split; assumption.
Qed.

Lemma group_left_cancellation `(G : Group) : forall k x y,
  k & x == k & y -> x == y.
Proof.
  intros k x y Q.
  assert (k ' & (k & x) == k ' & (k & y)) as Q' by (rewrite Q; reflexivity).
  repeat rewrite associativity in Q'.
  repeat rewrite leftInverse in Q'.
  repeat rewrite leftIdentity in Q'.
  assumption.
Qed.

Lemma group_right_cancellation `(G : Group) : forall k x y,
  x & k == y & k -> x == y.
Proof.
  intros k x y Q.
  assert ((x & k) & k ' == (y & k) & k ') as Q' by (rewrite Q; reflexivity).
  repeat rewrite <- associativity in Q'.
  repeat rewrite rightInverse in Q'.
  repeat rewrite rightIdentity in Q'.
  assumption.
Qed.

Theorem group_inverse_over_product `(G : Group) : forall x y,
  (x & y) ' == y ' & x '.
Proof.
  intros x y.
  assert ((x & y) & (y ' & x ') == identity) as Q.
  assert ((x & y) & (y ' & x ') == x & (y & y ') & x ') as Q by (repeat rewrite associativity; reflexivity).
  rewrite Q.
  rewrite rightInverse.
  rewrite rightIdentity.
  rewrite rightInverse.
  reflexivity.
  destruct (group_unique_inverses _ _ _ Q).
  symmetry; assumption.
Qed.

Theorem group_inverse_inverse `(G : Group) : forall a,
  a ' ' == a.
Proof.
  intro.
  assert (a ' & a == identity) as Q by apply leftInverse.
  destruct (group_unique_inverses _ _ _ Q).
  symmetry; assumption.
Qed.

(** tests

Theorem group_test `(G : Group) :
  forall x,
    x & x ' == identity.
intros.
rewrite rightInverse.
reflexivity.
Qed.

**)
