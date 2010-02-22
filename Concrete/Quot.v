Require Import
 Technology.Setoid
 Technology.Nonzero
 Abstract.Magma
 Abstract.Abelian
 Abstract.Semigroup
 Abstract.Monoid
 Abstract.Group
 Abstract.Ring
 Abstract.IntegralDomain
 Abstract.Field.

Section FieldOfQuotients.

Variables
  (M : Setoid)
  (m : Magma M)
  (m' : Magma M)
  (s : Semigroup M m)
  (mo : Monoid M m s)
  (a : Abelian M m)
  (s' : Semigroup M m')
  (mo' : Monoid M m' s')
  (g : Group M m s mo)
  (a' : Abelian M m')
  (i : IntegralDomain M m m' s mo s' mo').

Definition zero := identity M m s mo.
Definition one := identity M m' s' mo'.

Program Definition Quot : Setoid :=
  Build_Setoid
    (car M * car (Nonzero M zero))
    (fun x y =>
      let (p,q) := x in
      let (u,v) := y in
        (* p/q = u/v  <=>  pv = uq *)
        eq M (operation M m' p (proj1_sig v)) (operation M m' u (proj1_sig q)))
    _
    _
    _.
Next Obligation.
unfold Relation_Definitions.reflexive.
intros; destruct x.
reflexivity.
Qed.
Next Obligation.
unfold Relation_Definitions.symmetric.
intros; destruct x; destruct y.
symmetry.
apply H.
Qed.
Next Obligation.
unfold Relation_Definitions.transitive.
intros; destruct x; destruct y; destruct z.
destruct s0.
destruct s1.
destruct s2.
simpl in *.
rename c into aa; rename c0 into bb.
rename x into cc; rename x0 into dd.
rename c1 into ee; rename x1 into ff.
(*
ad = bc
bf = ed
*)
(*
adbf = bced
*)
assert (
  eq M (operation M m' (operation M m' aa dd)
                       (operation M m' bb ff))
       (operation M m' (operation M m' bb cc)
                       (operation M m' ee dd))
).

rewrite H.
rewrite H0.
reflexivity.
clear H; clear H0.
(*
af(db) = ec(db)
*)
assert (
  eq M (operation M m' (operation M m' aa dd) (operation M m' bb ff))
       (operation M m' (operation M m' aa ff) (operation M m' dd bb))
).
admit.
assert (
  eq M (operation M m' (operation M m' bb cc) (operation M m' ee dd))
       (operation M m' (operation M m' ee cc) (operation M m' dd bb))
).
admit.
rewrite H in H1.
rewrite H0 in H1.
(*
af = ec
*)
Admitted.

End FieldOfQuotients.
