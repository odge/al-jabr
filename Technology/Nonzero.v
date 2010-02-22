Require Import
  Technology.Setoid.

Program Definition Nonzero (M : Setoid) (zero : car M) : Setoid :=
  Build_Setoid
    { m : car M | ~ eq M m zero }
    (fun x y => eq M (proj1_sig x) (proj1_sig y))
    _
    _
    _.
Next Obligation.
unfold Relation_Definitions.reflexive.
intros; destruct x.
simpl in *.
reflexivity.
Qed.
Next Obligation.
unfold Relation_Definitions.symmetric.
intros; destruct x; destruct y.
simpl in *.
symmetry.
assumption.
Qed.
Next Obligation.
unfold Relation_Definitions.transitive.
intros; destruct x; destruct y; destruct z.
simpl in *.
transitivity x0.
assumption.
assumption.
Qed.

