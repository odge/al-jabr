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

Require Import Program.

Program Definition Quot {S : Setoid} `(I : Integral S) (AddAbl : @Abelian _ _ Add) (MulAbl : @Abelian _ _ Mul) : Setoid :=
  let quot_eq := fun (x y : S * S) =>
    let (p,q) := x in
    let (u,v) := y in
      (* p/q = u/v  <=>  pv = uq *)
      p (x) v == u (x) q
      in
  Build_Setoid
    ({ (x, y) : S * S | y # zero })
    quot_eq
    (fun x y => ~ quot_eq x y)
    _
    _
    _
    _.
Next Obligation.
unfold reflexive.
destruct x as [[p q] xPrf].
simpl.
reflexivity.
Qed.
Next Obligation.
unfold symmetric.
destruct x as [[p q] xPrf]; destruct y as [[u v] yPrf].
simpl.
intro; symmetry; congruence.
Qed.
Next Obligation.
unfold transitive.
destruct x as [[p q] xPrf]; destruct y as [[u v] yPrf]; destruct z as [[m n] zPrf].
simpl.
intros Q Q'.

pose (fun a b => integral_left_cancellation _ _ a b xPrf) as x.
pose (fun a b => integral_left_cancellation _ _ a b yPrf) as y.
pose (fun a b => integral_left_cancellation _ _ a b zPrf) as z.

apply x; apply y; apply z.

rewrite (@commutativity Multiplicative _ _ _ p).
repeat rewrite <- associativity.
rewrite (@commutativity Multiplicative _ _ _ v).
repeat rewrite <- associativity.
rewrite Q.

rewrite (@commutativity Multiplicative _ _ _ m).
repeat rewrite <- associativity.
rewrite (@commutativity Multiplicative _ _ _ v).
repeat rewrite <- associativity.
rewrite <- Q'.

repeat rewrite (@commutativity Multiplicative _ _ _ n).
repeat rewrite <- associativity.
repeat rewrite (@commutativity Multiplicative _ _ _ q).
repeat rewrite <- associativity.
repeat rewrite (@commutativity Multiplicative _ _ _ u).
repeat rewrite <- associativity.

reflexivity.
Qed.
