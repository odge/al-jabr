Require Import
 Technology.FirstClassSetoid
 Abstract.Algebra
 Concrete.N.

Require Import Arith.

Definition int := (nat * nat)%type.
Definition int_equal (p q : int) :=
  let (u,v) := p in
  let (x,y) := q in
(* u - v = x - y  <=> *) (u + y = x + v)%nat.

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
assert (((a + d) + (c + f) = (c + b) + (e + d))%nat) as Q' by (rewrite Q1; rewrite Q2; reflexivity).
repeat rewrite plus_assoc in Q'.
cut (((d + c) + (a + f) = (d + c) + (e + b))%nat).
apply plus_reg_l.
clear Q1; clear Q2.
rewrite plus_permute.
repeat rewrite plus_assoc.
rewrite Q'.
ring.
Qed.
