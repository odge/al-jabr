Require Import Equivalence Relation_Definitions.
Require Export Morphisms Setoid.

Record Setoid : Type := {
  car : Type ;
  eq : car -> car -> Prop ;
  apart : car -> car -> Prop ;
  refl : reflexive _ eq ;
  sym : symmetric _ eq ;
  trans : transitive _ eq
}.

Notation "x == y" := (eq _ x y) (at level 70, no associativity).
Notation "x # y" := (apart _ x y) (at level 70, no associativity).
Coercion car : Setoid >-> Sortclass.

Record Morphism (S1 S2 : Setoid): Type := {
  f : car S1 -> car S2 ;
  compat : forall (x1 x2 : car S1), eq S1 x1 x2 -> eq S2 (f x1) (f x2)
}.

Add Parametric Relation (s : Setoid) : (@car s) (@eq s)
 reflexivity proved by (refl s)
 symmetry proved by (sym s)
 transitivity proved by (trans s) as eq_rel.

Add Parametric Morphism (S1 S2 : Setoid) (M : Morphism S1 S2) :
 (@f S1 S2 M) with signature (@eq S1 ==> @eq S2) as apply_mor.
Proof. apply (compat S1 S2 M). Qed.
