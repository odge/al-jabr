Require Import
 Technology.Setoid
 Abstract.Magma
 Abstract.Abelian
 Abstract.Semigroup.

Definition int : Set := (nat * nat)%type.

Definition int_equal (p q : int) :=
  let (u,v) := p in
  let (x,y) := q in
(* u - v = x - y  <=> *)  u + y = x + v.

Program Definition Z : Setoid := Build_Setoid int int_equal _ _ _.
Next Obligation.
unfold Relation_Definitions.reflexive.
unfold int_equal; destruct x.
reflexivity.
Qed.
Next Obligation.
unfold Relation_Definitions.symmetric.
unfold int_equal; destruct x; destruct y.
congruence.
Qed.
Next Obligation.
unfold Relation_Definitions.transitive.
unfold int_equal; destruct x; destruct y; destruct z.

Require Import Arith.
SearchAbout nat.
Admitted.

Definition int_plus (p q : car Z) : car Z :=
  let (u,v) := p in
  let (x,y) := q in
  (u+x,v+y).

Program Definition int_magma_additive : Magma Z := Build_Magma Z int_plus _.
Next Obligation.
unfold Proper.
unfold respectful.
intros.
unfold int_equal.
unfold int_plus.
destruct x; destruct y; destruct x0; destruct y0.
simpl in *.
Admitted.

