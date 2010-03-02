Require Import
 Technology.FirstClassSetoid
 Abstract.Algebra.

Require Import Arith.
Require Import Program.

Program Definition Quot {S : Setoid} `(I : Integral S) (AddAbl : @Abelian _ _ Add) (MulAbl : @Abelian _ _ Mul) : Setoid :=
  let quot_eq := fun (x y : S * S) =>
    let (p,q) := x in
    let (u,v) := y in
      (* p/q = u/v  <=>  pv = uq *)
      p * v == u * q
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



