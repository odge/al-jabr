Require Import NPeano Arith.

Fixpoint C (n k : nat) :=
  match n, k with
    | _, 0 => 1
    | 0, _ => 0
    | S n, S k => C n k + C n (S k)
  end.

Lemma C_prop_1 {n} : C n 0 = 1.
Proof.
  destruct n; reflexivity.
Qed.

Lemma C_prop_3 n d : C n (n + S d) = 0.
Proof.
  induction n.
  reflexivity.
  simpl; intro.
  assert (S (n + S d) = n + S (S d)) as Q by auto with arith. 
  rewrite Q.
  rewrite (IHn d).
  rewrite (IHn (S d)).
  reflexivity.
Qed.

Lemma C_prop_2 {n} : C n n = 1.
Proof.
  induction n.
  reflexivity.
  simpl.
  rewrite IHn.
  rewrite <- (Nat.add_1_r n).
  rewrite (C_prop_3 n 0).
  reflexivity.
Qed.

Lemma C_prop_4 {n k} : C (S n) (S k) = C n k + C n (S k).
Proof.
  reflexivity.
Qed.


Definition Sum f n :=
  (fix Sum k :=
    match k with
      | O => f 0
      | S k => Sum k + f (S k)
    end) n.

Theorem Sum_prop_1 {f n} : Sum f (S n) = Sum f n + f (S n).
Admitted.

Theorem Sum_prop_2 {f n} : Sum f (S n) = f 0 + Sum (fun k => f (S k)) n.
Admitted.

Fixpoint pow n k :=
  match k with
    | O => 1
    | S k => n * pow n k
  end.

Theorem binomial x : forall n, pow (x + 1) n = Sum (fun k => C n k * pow x k) n.
Proof.
Admitted.
