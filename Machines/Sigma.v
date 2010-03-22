Require Import
  Technology.FirstClassSetoid
  Abstract.Magma
  Abstract.Semigroup
  Abstract.Abelian
  Abstract.Monoid
  Abstract.Group
  Abstract.Ring.
Require Import Arith List.

Theorem why_is_this_not_standard {a b} : b > a -> { d : nat | b = plus a (S d) }.
Proof.
  intros a b H.
  induction a.
  simpl in *.
  destruct b.
  apply False_rect.
  inversion H.
  exists b; reflexivity.
  assert (b > a) as Q by auto with arith.
  destruct (IHa Q).
  destruct x.
  rewrite e in H.
  apply False_rect.
  rewrite plus_comm in H.
  apply (gt_irrefl _ H).
  exists x.
  rewrite e.
  ring.
Qed.
Definition gt_subtract := @why_is_this_not_standard.


Section Sigma.
Context `(C : Setoid).
Context `(R : Ring C).

Fixpoint nats_from (x: nat) (c: nat): list nat :=
  match c with
  | 0 => nil
  | S c' => x :: nats_from (S x) c'
  end.

Definition sum: list C -> C :=
  fold_right (fun x y => x + y) zero.

Definition Sigma (a b: nat) (f: nat -> C) (* Thanks to Eelis! *)
  := sum (map f (nats_from a (b-a))).

Lemma Sigma_prop_1a {a b f} : b > a -> Sigma a b f == f a + Sigma (S a) b f.
Proof.
  unfold Sigma; intros.
  destruct (why_is_this_not_standard H).
  assert (b - a = S x).
  rewrite e.
  rewrite minus_plus.
  reflexivity.
  rewrite H0.
  pose (NPeano.Nat.sub_succ_r b a).
  rewrite H0 in e0.
  rewrite <- pred_Sn in e0.
  rewrite e0.
  reflexivity.
Qed.

Lemma Sigma_prop_1b {a b f} : b > a -> Sigma a (S b) f == Sigma a b f + f b.
Proof.
  unfold Sigma; intros.
  destruct (why_is_this_not_standard H).
  assert (b - a = S x).
  rewrite e.
  rewrite minus_plus.
  reflexivity.
  rewrite H0.
  rewrite <- minus_Sn_m.
  rewrite H0.
  rewrite e.
  
  clear e H0.
  revert f.
  induction x.
  simpl.
  rewrite plus_comm.
  simpl.
  intro.
  rewrite <- (@commutativity _ _ _ _ zero).
  rewrite associativity.
  reflexivity.
(** somethings wrong.. this should not be this difficult **)
Admitted.

End Sigma.
