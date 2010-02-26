Require Import
  Technology.Setoid.

Inductive Tag := Additive | Multiplicative.

Class Magma (tag : Tag) (M : Setoid) := {
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
intros tag M m x y a Q.
rewrite Q; reflexivity.
Qed.

(************)

Notation "x (+) y" := (@operation Additive _ _ x y) (at level 50, no associativity).
Notation "x '(x)' y" := (@operation Multiplicative _ _ x y) (at level 40, no associativity).

Definition mul_add_test `(m : Magma Additive) `(m' : Magma Multiplicative M) x y := x (+) y (x) x.


