Require Import
  Technology.FirstClassSetoid
  Abstract.Magma
  Abstract.Semigroup
  Abstract.Abelian
  Abstract.Monoid
  Abstract.Group
  Abstract.Ring.
Require Import Arith List.

Section Sigma.
Context `(car : Setoid).
Context `(R : Ring car).
Variable X : Type.

Fixpoint Σ (elements : list X) (f : X -> car) : car :=
  match elements with
    | nil => zero
    | x :: xs => f x + Σ xs f
  end.

Lemma Σ_prop_1 u v f : Σ u f + Σ v f == Σ (u ++ v) f.
Proof.
  intros; induction u; simpl.
  rewrite leftIdentity; reflexivity.
  rewrite <- IHu.
  rewrite associativity.
  reflexivity.
Qed.

Lemma Σ_prop_2 a u f : Σ (a::u) f == f a + Σ u f.
Proof.
  reflexivity.
Qed.

Lemma Σ_prop_3 u a f : Σ (u++a::nil) f == Σ u f + f a.
Proof.
  intros; induction u; simpl.
  rewrite leftIdentity; rewrite rightIdentity; reflexivity.
  rewrite IHu.
  rewrite associativity; reflexivity.
Qed.

Lemma Σ_prop_distributivity k u f : Σ u (fun i => k * f i) == k * Σ u f.
Proof.
  intros; induction u; simpl.
  rewrite ring_zero_absorbant_right.
  reflexivity.
  assumption. (*?*)
  rewrite IHu.
  rewrite leftDistributivity.
  reflexivity.
Qed.

Lemma Σ_prop_distributivity' a b u f : Σ u (fun i => (a i + b i) * f i) == Σ u (fun i => a i * f i) + Σ u (fun i => b i * f i).
Proof.
  intros; induction u; simpl.
  rewrite leftIdentity.
  reflexivity.
  rewrite IHu.
  rewrite rightDistributivity.
  repeat rewrite <- associativity.
  repeat rewrite (associativity _ (b a0 * f a0)).
  rewrite (commutativity (Σ u (fun i => a i * f i)) (b a0 * f a0)).
  repeat rewrite associativity.
  reflexivity.
Qed.

Lemma Σ_prop_distributivity'' a b u : Σ u (fun i => a i + b i) == Σ u (fun i => a i) + Σ u (fun i => b i).
Proof.
  intros; induction u; simpl.
  rewrite leftIdentity.
  reflexivity.
  rewrite IHu.
  rewrite (associativity _ (b a0)).
  repeat rewrite <- (associativity (a a0)).
  rewrite (commutativity _ (b a0)).
  repeat rewrite associativity.
  reflexivity.
Qed.

Lemma Σ_map u f m : Σ (map m u) f == Σ u (fun i => f (m i)).
Proof.
  intros; induction u; simpl.
  reflexivity.
  rewrite IHu.
  reflexivity.
Qed.

Lemma Σ_extensionality u f g : (forall x, f x == g x) -> Σ u f == Σ u g.
Proof.
  intros u f g Q; induction u.
  reflexivity.
  simpl; rewrite Q; rewrite IHu.
  reflexivity.
Qed.

Fixpoint ι (n : nat) :=
  match n with
    | O => nil
    | S n => ι n
  end ++ n::nil.

Lemma ι_prop_2 {n} : ι (S n) = ι n ++ S n :: nil.
Proof.
  reflexivity.
Qed.

Lemma ι_prop_1 {n} : ι (S n) = 0 :: map S (ι n).
Proof.
  induction n.
  reflexivity.
  rewrite ι_prop_2.
  rewrite IHn at 1.
  rewrite <- app_comm_cons.
  cut (map S (ι n) ++ S (S n)::nil = map S (ι (S n))).
  intro Q; rewrite Q; reflexivity.
  clear IHn; induction n.
  reflexivity.
  rewrite <- IHn.
  simpl.
  repeat rewrite map_app.
  repeat rewrite app_ass.
  reflexivity.
Qed.

End Sigma.

Implicit Arguments Σ [car0 Add AddMon X].
