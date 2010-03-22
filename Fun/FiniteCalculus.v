(** Following www.stanford.edu/~dgleich/publications/finite-calculus.pdf **)
(* (except for there's a minor twiddle when it comes do the FTFC) *)

Require Import ZArith.
Open Local Scope Z_scope.

Definition DiscreteDerivative (f : Z -> Z) (x : Z) := f (x + 1) - f x.
Notation "∆" := DiscreteDerivative.

Fact dd_x x : ∆ (fun x => x) x = 1.
Proof.
  unfold DiscreteDerivative; intro.
  ring.
Qed.

Theorem dd_Scalar_Law k f x : ∆ (fun x => k * f x) x = k * ∆ f x.
Proof.
  unfold DiscreteDerivative; intros.
  ring.
Qed.

Theorem dd_Sum_Law f g x : ∆ (fun x => f x + g x) x = ∆ f x + ∆ g x.
Proof.
  unfold DiscreteDerivative; intros.
  ring.
Qed.

Theorem dd_Product_Law f g x : ∆ (fun x => f x * g x) x = f x * ∆ g x + g (x + 1) * ∆ f x.
Proof.
  unfold DiscreteDerivative; intros.
  ring.
Qed.

Fact dd_x_x1 x : ∆ (fun x => x * (x - 1)) x = 2 * x.
Proof.
  unfold DiscreteDerivative; intro.
  ring.
Qed.

Fact dd_x_x1_x2 x : ∆ (fun x => x * (x - 1) * (x - 2)) x = 3 * x * (x - 1).
Proof.
  unfold DiscreteDerivative; intro.
  ring.
Qed.

Fixpoint Falling_Power (x : Z) (m : nat) : Z :=
  match m with
    | O => 1
    | S m => x * Falling_Power (x - 1) m
  end.
Infix "^^" := Falling_Power (at level 20).

Ltac refold f := unfold f; fold f.

Fact Z_of_nat_S_through m :
  Z_of_nat (S (S m)) =
  1 + Z_of_nat (S m).
Proof.
  simpl; intro.
  destruct (P_of_succ_nat m);
    reflexivity.
Qed.

Fact Z_of_nat_S_through' n :
  1 + Z_of_nat n =
  Z_of_nat (S n).
Proof.
  unfold Z_of_nat; intro.
  destruct n.
  reflexivity.
  unfold P_of_succ_nat.
  rewrite Pplus_one_succ_l.
  fold P_of_succ_nat.
  reflexivity.
Qed.

Lemma Falling_Power_backward m x : x^^S m = x^^m*(x-Z_of_nat (S m)+1).
Proof.
  induction m; intro.
  
  simpl.
  ring_simplify (x * 1).
  ring_simplify (x - 1 + 1).
  destruct x; reflexivity.
  
  assert (
    x ^^ S (S m) =
    x * (x - 1) ^^ S m
  ) as Q by reflexivity.
  rewrite Q.
  rewrite IHm.
  rewrite Z_of_nat_S_through.
  refold Falling_Power.
  ring.
Qed.

Theorem dd_Exponent_Law m x : ∆ (fun x => x ^^ S m) x = Z_of_nat (S m) * x ^^ m.
Proof.
(* The proof is just algebra, ∆ x^m = m*x^(m-1)
     ∆ x^m
   = (x+1)^m - x^m
   = (x+1)*x^(m-1) - x^(m-1)*(x-m+1)
   = (x+1 - x+m-1)*x^(m-1)
   = m*x^(m-1)
*)
  unfold DiscreteDerivative; intros.
  
  rewrite (Falling_Power_backward m x).
  refold Falling_Power.
  ring_simplify (x + 1 - 1).
  assert (
    (x + 1) * x ^^ m - x ^^ m * (x - Z_of_nat (S m) + 1) =
    (x + 1 - x + Z_of_nat (S m) - 1) * x ^^ m
  ) as Q by ring.
  rewrite Q.
  
  ring.
Qed.

Fixpoint Sigma n a f :=
  match n with
    | O => 0
    | S n => f a + Sigma n (a + 1) f
  end.

Definition Discrete_Definite_Integral a b f :=
  match b - a with
    | Zpos p => Sigma (nat_of_P p) a f
    | _ => 0
  end.

Theorem Fundamental_Theorem_Of_Finite_Calculus a b f : a < b ->
  Discrete_Definite_Integral a b (∆ f) = f b - f a.
Proof.
  unfold Discrete_Definite_Integral; intros.
  assert (b > a) as H' by omega.
  destruct (Zcompare_Gt_spec b a H') as [p pPrf].
  ring_simplify in pPrf.
  rewrite pPrf.
  
  Lemma Fundamental_Theorem_Sigma_Lemma f n a :
    Sigma n a (∆ f) = f (a + Z_of_nat n) - f a.
  Proof.
    induction n; intro.
    simpl.
    ring_simplify (a + 0).
    ring.
    refold Sigma.
    unfold DiscreteDerivative.
    cut (
      f (a + 1) + Sigma n (a + 1) (fun x : Z => f (x + 1) - f x) =
      f (a + Z_of_nat (S n))
    ).
    intro H; rewrite <- H; ring.
    rewrite IHn.
    ring_simplify.
    assert (
      1 + Z_of_nat n =
      Z_of_nat (S n)
    ) as Q.
    apply Z_of_nat_S_through'.
    rewrite <- Q.
    ring_simplify (a + 1 + Z_of_nat n).
    ring_simplify (a + (1 + Z_of_nat n)).
    reflexivity.
  Qed.
  
  assert (b = a + Z_of_nat (nat_of_P p)) as Q.
  rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P.
  rewrite <- pPrf.
  ring.
  rewrite Q.
  apply Fundamental_Theorem_Sigma_Lemma.
Qed.

