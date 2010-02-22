Require Import
  Technology.Setoid
  Technology.Nonzero
  Abstract.Magma
  Abstract.Abelian
  Abstract.Semigroup
  Abstract.Monoid
  Abstract.Group
  Abstract.Ring.

Record Field (M : Setoid) (m : Magma M) (m' : Magma M) (s : Semigroup M m) (mo : Monoid M m s) (a : Abelian M m) (s' : Semigroup M m') (mo' : Monoid M m' s') (g : Group M m s mo)
  (r : Ring M m m' s mo a s' mo' g)
  prf1 prf2
  (g' : Group
    (Nonzero M (identity M m s mo))
    (Magma_Nonzero M (identity M m s mo) m' prf1)
    (Semigroup_Nonzero M (identity M m s mo) m' s' prf1)
    (Monoid_Nonzero M (identity M m s mo) m' s' mo' prf1 prf2)) := {}.
