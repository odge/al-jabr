Require Import
  Technology.FirstClassSetoid
  Technology.Tag
  Abstract.Magma
  Abstract.Semigroup
  Abstract.Monoid
  Abstract.Group
  Abstract.Ring.

Set Automatic Introduction.

Delimit Scope algebra_scope with algebra.
Open Scope algebra_scope.

Class Integral `(R : Ring) := {
  nonDegernerate : one # zero ;
  noZeroDivisors : forall a b,
    a * b == zero -> a == zero \/ b == zero
}.

Theorem integral_left_cancellation `(I : Integral) : forall k a b,
  k # zero -> k * a == k * b -> a == b.
Proof.
  intros k a b.
  intros kNonzero Q.
  assert (k * a + (k * b) ' == zero) as Q'.
  rewrite Q.
  rewrite rightInverse.
  reflexivity.
  rewrite <- ring_negate_bubble_right in Q'; try assumption. (** not good!! **)
  rewrite <- leftDistributivity in Q'.
  destruct (noZeroDivisors _ _ Q') as [|N].
  pose (nonequal _ _ _ kNonzero).
  contradiction.
  destruct (group_unique_inverses _ _ _ N) as [N' N''].
  rewrite group_inverse_inverse in N'.
  assumption.
Qed.
