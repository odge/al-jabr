Require Import Arith ZArith Znumtheory.

Require Import Program.

Program Fixpoint divisibility_test (i n : Z)
  {measure (
    if Z_lt_dec n 0
      then S (S (Zabs_nat n + Zabs_nat i))
      else if Z_lt_dec i 0
        then S (Zabs_nat n + Zabs_nat i)
        else Zabs_nat n)}
  : option (i | n) :=
  if Z_eq_dec i 0 then None else
  if Z_lt_dec n 0
    then if divisibility_test i (- n)
      then Some _
      else None
    else if Z_lt_dec i 0
      then if divisibility_test (- i) n
        then Some _
        else None
      else if Z_eq_dec i n
        then Some _
        else if Z_lt_dec i n
          then if divisibility_test i (n - i)
            then Some _
            else None
          else None.

Next Obligation.
destruct (Z_lt_dec (- n) 0).
elimtype False; omega.
destruct (Z_lt_dec i 0).
destruct (Z_lt_dec n 0).
pose (Zabs_nat_mult (-1) n) as Q.
assert (-1 * n = - n) as Q' by ring.
rewrite Q' in Q.
rewrite Q.
simpl.
omega.
elimtype False.
omega.
destruct (Z_lt_dec n 0).
pose (Zabs_nat_mult (-1) n) as Q.
assert (-1 * n = - n) as Q' by ring.
rewrite Q' in Q.
rewrite Q.
simpl.
omega.
elimtype False.
omega.
Defined.

Next Obligation.
apply Zdivide_opp_r_rev; assumption.
Defined.

Next Obligation.
destruct (Z_lt_dec n 0).
pose (Zabs_nat_mult (-1) i) as Q.
assert (-1 * i = - i) as Q' by ring.
rewrite Q' in Q.
rewrite Q.
simpl.
omega.
destruct (Z_lt_dec i 0); destruct (Z_lt_dec (- i) 0);
  try (elimtype False; omega).
omega.
Defined.

Next Obligation.
apply Zdivide_opp_l_rev.
assumption.
Defined.

Next Obligation.
apply Zdivide_refl.
Defined.

Next Obligation.
destruct (Z_lt_dec (n - i) 0);
  destruct (Z_lt_dec n 0);
    destruct (Z_lt_dec i 0);
      try (elimtype False; omega).
apply Zabs_nat_lt.
split; omega.
Defined.

Next Obligation.
assert (n = (n - i) + i) as Q by ring; rewrite Q.
apply Zdivide_plus_r; [ assumption | apply Zdivide_refl ].
Defined.

Program Fixpoint prove_bounded_universal {P}
  (d : nat) (a : Z) (test : forall i : Z, option (P i))
  : option (forall i, a < i < (a + Z_of_nat (S d)) -> P i) :=
  match d with
    | O => Some _
    | S d =>
      if prove_bounded_universal d a test
        then if test (a + Z_of_nat (S d))
          then Some _
          else None
        else None
  end.

Next Obligation.
elimtype False.
omega.
Defined.

Next Obligation.

destruct (Z_eq_dec i (a + Zpos (P_of_succ_nat d0))).

rewrite e.
assumption.

apply H.
split; auto.

assert (i <= a + Zpos (P_of_succ_nat d0)).
rewrite Zpos_P_of_succ_nat in *.
rewrite Zpos_succ_morphism in *.
rewrite <- Z.add_1_l in *.
assert (Zsucc 0 = 1) as Q by reflexivity; rewrite Q in *.
SearchAbout [Zpos P_of_succ_nat].
rewrite Zpos_P_of_succ_nat in *.
omega.
apply Z.T.le_neq_lt.
assumption.
assumption.
Defined.

Program Definition indivisibility_test (i n : Z)
  : option (~ (i | n)) :=
  if Z_eq_dec (Zmod n i) 0
    then None
    else Some _.

Next Obligation.
intro.
apply H.
apply Zdivide_mod.
assumption.
Defined.

Definition isSome {T} (s : option T) :=
  match s with
    | Some _ => true
    | None => false
  end.

Definition prime_test (n : Z) : option (prime' n).
refine (
  fun n =>
    if Z_lt_dec 1 n
      then if prove_bounded_universal (Zabs_nat (n - 2)) 1 (fun i => indivisibility_test i n)
        then Some _
        else None
      else None
).
unfold prime'.
split; [assumption|].
intro i.

SearchAbout [Z_of_nat S].
rewrite inj_S in _H0.
rewrite inj_Zabs_nat in _H0.
assert (0 <= n - 2) by omega.
rewrite (Zabs_eq _ H) in _H0.
ring_simplify (1 + Zsucc (n - 2)) in _H0.
intro.
apply _H0.
destruct H0.
split; omega.
Defined.

Theorem prime_test_sound (n : Z) : if isSome (prime_test n) then prime n else True.
intro.
destruct (prime_test n); simpl; trivial.
destruct (prime_alt n).
apply H; assumption.
Qed.

Ltac prove_prime :=
  match goal with
    | [ |- prime ?n ] => apply (prime_test_sound n)
  end.
