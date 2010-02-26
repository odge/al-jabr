Require Import
  Technology.Setoid
  Abstract.Magma
  Abstract.Abelian
  Abstract.Semigroup
  Abstract.Monoid
  Abstract.Group
  Abstract.Ring.

Class IntegralDomain `(r : Ring) := {
  zeroIsn'tOne : ~ zero == one ;
  zeroProduct : forall a b,
    a (x) b == zero -> a == zero \/ b == zero
}.

Theorem leftCancellation `(i : IntegralDomain) : forall k a b,
  ~ k == zero -> k (x) a == k (x) b -> a == b.
Proof.
intros.
assert (k (x) a (+) inverse (k (x) b) == zero).
rewrite H0.
apply rightInverse.
assert (k (x) a (+) k (x) inverse b == zero).
admit.
assert (k (x) (a (+) inverse b) == zero).
rewrite leftDistributivity.
apply H4.
destruct (zeroProduct _ _ H5).
contradiction.
assert (a (+) (inverse b (+) b) == b (+) (inverse b (+) b)).
rewrite <- associativity.
rewrite H6.
symmetry.
rewrite leftInverse.
rewrite leftIdentity.
rewrite rightIdentity.
reflexivity.
rewrite leftInverse in H7.
repeat rewrite rightIdentity in H7.
assumption.
Qed.
