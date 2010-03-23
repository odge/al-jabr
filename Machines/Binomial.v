Require Import
  Technology.FirstClassSetoid
  Abstract.Magma
  Abstract.Semigroup
  Abstract.Abelian
  Abstract.Monoid
  Abstract.Group
  Abstract.Ring
  Machines.Sigma.
Require Import Arith List.

Section Binomial.
Context `(car : Setoid).
Context `(R : Ring car).

Parameter inj : nat -> car.

Axiom C : nat -> nat -> nat.

Lemma C_prop_1 {n k} : C (S n) k = plus (C n k) (C n (pred k)).
Admitted.

Lemma C_prop_2 {n} : C n 0 = 1.
Admitted.

Lemma C_prop_3 {n} : C n n = 1.
Admitted.

Theorem binomial {x n} : (one + x) ^ n == Σ (ι n) (fun k => inj (C n k) * x ^ k).
Proof.
  induction n. 
  simpl.
  assert (inj (C 0 0) == one) as Q by admit; rewrite Q.
  do 2 rewrite rightIdentity; reflexivity.
  
  assert (
    forall k,
      (fun k : nat => inj (C (S n) k) * x ^ k) k ==
      (fun k : nat => (fun k => inj (C n k) * x ^ k) k + (fun k => inj (C n (pred k)) * x ^ k) k) k)
  as Ext.
  simpl; intro; rewrite C_prop_1.
  assert (forall a b, inj (a + b) = inj a + inj b) as Q' by admit.
  rewrite Q'.
  rewrite rightDistributivity.
  reflexivity.
  rewrite (Σ_extensionality _ _ _ _ _ Ext).
  rewrite Σ_prop_distributivity''.
  Focus 2.
  assumption.
  Focus 2.
  assumption.
  rewrite ι_prop_2 at 1.
  rewrite ι_prop_1 at 1.
  simpl.
  assert (inj (C n 0) == one) as Q by admit; rewrite Q.
  rewrite leftIdentity.
  rewrite Σ_map.
  simpl.
  rewrite Σ_prop_3.
  simpl.
  assert (inj (C n (S n)) == zero) as Q' by admit; rewrite Q'.
  rewrite ring_zero_absorbs_left.
  Focus 2.
  assumption.
  Focus 2.
  assumption.
  rewrite rightIdentity.
  rewrite IHn.
  rewrite rightDistributivity.
  rewrite leftIdentity.
  (* something has gone terribly terribly wrong here *)
Admitted.

