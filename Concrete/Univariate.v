Require Import
 Technology.FirstClassSetoid
 Technology.Tag
 Abstract.Algebra.

Require Import List.

Fixpoint list_equal {A} eq (x y : list A) :=
  match x, y with
    | nil, nil => True
    | x :: xs, y :: ys => eq x y /\ list_equal eq xs ys
    | _, _ => False
  end.

Program Definition Univariate {S : Setoid} : Setoid :=
  Build_Setoid
    (list S)
    (list_equal (fun x y => x == y))
    (fun x y => ~ list_equal (fun x y => x == y) x y)
    _
    _
    _
    _.
Next Obligation.
unfold reflexive.
induction x.
reflexivity.
split.
reflexivity.
assumption.
Qed.
Next Obligation.
unfold symmetric.
induction x; destruct y; try tauto.
simpl; intro H; destruct H.
split; [symmetry;assumption|].
apply IHx.
assumption.
Qed.
Next Obligation.
unfold transitive.
induction x; destruct y; destruct z; try tauto; simpl; try tauto.
intros H H'; destruct H; destruct H'.
split.
rewrite <- H1.
rewrite <- H.
reflexivity.
eapply IHx.
apply H0.
apply H2.
Qed.
