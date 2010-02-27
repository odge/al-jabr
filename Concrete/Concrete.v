Require Import
 Technology.FirstClassSetoid
 Abstract.Algebra.

Require Import Arith.

Program Definition N : Setoid := Build_Setoid nat (fun x y => x = y) (fun x y => x <> y) _ _ _ _.
Next Obligation.
unfold reflexive.
congruence.
Defined.
Next Obligation.
unfold symmetric.
congruence.
Defined.
Next Obligation.
unfold transitive.
congruence.
Defined.


Definition int := (nat * nat)% type.
Definition int_equal (p q : int) :=
  let (u,v) := p in
  let (x,y) := q in
(* u - v = x - y  <=> *)  u + y = x + v.

Program Definition Z : Setoid := Build_Setoid int int_equal (fun x y => ~ int_equal x y) _ _ _ _.
Next Obligation.
unfold int_equal.
unfold reflexive.
destruct x.
congruence.
Qed.
Next Obligation.
unfold int_equal.
unfold symmetric.
destruct x; destruct y.
congruence.
Qed.
Next Obligation.
unfold int_equal.
unfold transitive.
destruct x; destruct y; destruct z.

rename n into a.
rename n0 into b.
rename n1 into c.
rename n2 into d.
rename n3 into e.
rename n4 into f.

intros Q1 Q2.
assert ((a + d) + (c + f) = (c + b) + (e + d)) as Q' by (rewrite Q1; rewrite Q2; reflexivity).
repeat rewrite plus_assoc in Q'.
cut ((d + c) + (a + f) = (d + c) + (e + b)).
apply plus_reg_l.
clear Q1; clear Q2.
rewrite plus_permute.
repeat rewrite plus_assoc.
rewrite Q'.
ring.
Qed.


Program Definition Quot {S : Setoid} `(I : Integral S) : Setoid :=
  let quot_eq := fun (x y : S * S) =>
    let (p,q) := x in
    let (u,v) := y in
      (* p/q = u/v  <=>  pv = uq *)
      p (x) v == u (x) q
      in
  Build_Setoid
    (S * S)
    quot_eq
    (fun x y => ~ quot_eq x y)
    _
    _
    _
    _.
Next Obligation.
unfold reflexive.
destruct x.
reflexivity.
Qed.
Next Obligation.
unfold symmetric.
destruct x; destruct y.
intro; symmetry; congruence.
Qed.
Next Obligation.
unfold transitive.
destruct x; destruct y; destruct z.
intros Q Q'.

rename c into a.
rename c0 into b.
rename c1 into c.
rename c2 into d.
rename c3 into e.
rename c4 into f.

assert ((a(x)d)(x)(c(x)f) == (c(x)b)(x)(e(x)d)) as Q'' by (rewrite Q; rewrite Q'; reflexivity).
assert ((c(x)b)(x)(e(x)d) == c(x)((b(x)e)(x)d)) as RHS.
repeat rewrite associativity; reflexivity.
assert ((a(x)d)(x)(c(x)f) == c(x)((a(x)f)(x)d)) as LHS.
admit.

rewrite LHS in Q''; rewrite RHS in Q''.
pose (integral_left_cancellation _ _ _ _ _ Q'').

