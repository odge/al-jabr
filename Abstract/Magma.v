Require Import
  Technology.Nonzero
  Technology.Setoid.

Record Magma (M : Setoid) := {
  operation : car M -> car M -> car M ;
  operationRespectful : Proper (eq M ==> eq M ==> eq M) operation
}.

Add Parametric Morphism (M : Setoid) (m : Magma M) : (operation M m) with 
signature eq M ==> eq M ==> eq M as operation_mor.
Proof. exact (@operationRespectful M m). Qed.

Program Definition Magma_Nonzero (M : Setoid) (zero : car M) (m : Magma M) :
  forall prf1 : (forall x y : car M, ~ eq M x zero -> ~ eq M y zero -> ~ eq M (operation M m x y) zero),
  Magma (Nonzero M zero) :=
  fun prf1 =>
    Build_Magma
      (Nonzero M zero)
      (fun x y =>
        exist _ (operation M m (proj1_sig x) (proj1_sig y)) (prf1 (proj1_sig x) (proj1_sig y) (proj2_sig x) (proj2_sig y)))
      _.
Next Obligation.
unfold Proper.
unfold respectful.
simpl.
intros.
destruct x; destruct y; destruct x0; destruct y0.
simpl in *.
pose (operationRespectful M m).
unfold Proper in p.
unfold respectful in p.
apply p.
assumption.
assumption.
Qed.
