Require Import Technology.Setoid.

Record Magma (M : Setoid) := {
  operation : car M -> car M -> car M ;
  operationRespectful : Proper (eq M ==> eq M ==> eq M) operation
}.

