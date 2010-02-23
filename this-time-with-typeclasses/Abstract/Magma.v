Require Import
  Technology.Setoid.

Class Magma (M : Setoid) := {
  operation : car M -> car M -> car M ;
  operationRespectful : Proper (eq M ==> eq M ==> eq M) operation
}.
Infix "&" := operation (at level 20, no associativity).

Add Parametric Morphism `(m : Magma) : operation with 
signature eq M ==> eq M ==> eq M as operation_mor.
Proof. apply operationRespectful. Qed.

(************)

Lemma magma_morph_test `{m : Magma} : forall x y a,
  x == y -> a&x == a&y.
intros M m x y a Q; rewrite Q; reflexivity.
Qed.

(************)

Class MultiplicativeMagma `(Magma) := {}.
Class AdditiveMagma `(Magma) := {}.

Definition getMultiplicative `(MultiplicativeMagma) : Magma M.
intros.
assumption.
Defined.

Definition getAdditive `(AdditiveMagma) : Magma M.
intros.
assumption.
Defined.

Notation "x (+) y" := (@operation _ (getAdditive _) x y) (at level 50, no associativity).
Notation "x '(x)' y" := (@operation _ (getMultiplicative _) x y) (at level 40, no associativity).

Definition mul_add_test `(m : AdditiveMagma) `(m' : MultiplicativeMagma M) x y := x (+) y (x) x.
