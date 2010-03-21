Require Import
  Technology.FirstClassSetoid
  Technology.Tag
  Abstract.Magma
  Abstract.Semigroup
  Abstract.Monoid
  Abstract.Group.

Set Automatic Introduction.

Delimit Scope algebra_scope with algebra.
Open Scope algebra_scope.

Class Ring (S : Setoid) `(Add : Magma Additive S) `(Mul : Magma Multiplicative S)
  (AddSem : @Semigroup _ _ Add) (MulSem : @Semigroup _ _ Mul)
  (AddMon : @Monoid _ _ Add) (MulMon : @Monoid _ _ Mul)
  (AddGrp : @Group _ _ Add AddSem AddMon) := {
  leftDistributivity : forall k a b,
    k * (a + b) == k * a + k * b ;
  rightDistributivity : forall k a b,
    (a + b) * k == a * k + b * k
}.

(* A unit is an element that has a multiplicative inverse *)
Definition Unit {S} `(R : Ring S) : S -> Prop :=
  fun a =>
    exists b,
      a * b == one.

Theorem ring_Unit_one `{R : Ring} : Unit R one.
exists one; rewrite leftIdentity; reflexivity.
Qed.

Lemma ring_zero_absorbs_right `(R : Ring) : forall x,
  x * zero == zero.
Proof. (* x*0=x*0+((x*0)+-(x*0))=x*(0+0)*-x*0=x*0+-x*0=0 *)
  intros x.
  assert (x*zero == x*zero + x*zero + (x*zero)') as Q.
  rewrite <- associativity.
  rewrite rightInverse.
  rewrite rightIdentity.
  reflexivity.
  rewrite Q.
  rewrite <- leftDistributivity.
  rewrite leftIdentity.
  rewrite rightInverse.
  reflexivity.
Qed.

Lemma ring_zero_absorbant_right `(R : Ring) :
  forall a, a * zero == zero.
Proof.
  intro a.
  assert (a + zero == a) as Q by (rewrite rightIdentity; reflexivity).
  assert (a * (a + zero) == a * a) as Q' by (rewrite Q; reflexivity).
  rewrite leftDistributivity in Q'.
  exact (group_unique_identity_right _ _ _ Q').
Qed.

Theorem ring_negate_bubble_right `(R : Ring) : forall a b,
  a * b ' == (a * b) '.
Proof. (* 0 = a(0) = a(b+(-b)) = ab + a(-b) ==> ab = -a(-b) ==> -ab = --a(-b) = a(-b) *)
  intros.
  assert (zero == a * b + a * b ') as Q.
  rewrite <- leftDistributivity.
  rewrite rightInverse.
  rewrite ring_zero_absorbs_right.
  reflexivity.
  assumption. (** This goal is bad news! **)
  assert ((a*b)'+zero == (a*b)'+a*b+a*b ') as Q'.
  rewrite Q.
  rewrite associativity.
  reflexivity.
  rewrite leftInverse in Q'.
  rewrite leftIdentity in Q'.
  rewrite rightIdentity in Q'.
  symmetry; assumption.
Qed.

Lemma ring_negate `(R : Ring) : forall x, x * one ' == x '.
Proof.
  intros.
  rewrite ring_negate_bubble_right.
  rewrite rightIdentity.
  reflexivity.
  assumption.
Qed.

Theorem neg_times_neg_positive `(R : Ring) : one ' * one ' == one.
Proof. (* this formally disproves the cubic "truth" of -1 * -1 = -1 in ring theory *)
  rewrite <- (group_inverse_inverse AddGrp one) at 3.
  rewrite <- (ring_negate R (one ')).
  reflexivity.
Qed.
