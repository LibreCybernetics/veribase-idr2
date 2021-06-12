module Data.PrimInteger

import Builtin

import Algebra.Relation.Equivalence
import Algebra.Relation.Preorder
import Algebra.Relation.Order

%default total

public export
Equivalence Integer where
  Equiv x y = (prim__eq_Integer x y = 1)

  decEquiv x y with (prim__eq_Integer x y)
    decEquiv _ _ | 1 = Yes Refl
    decEquiv _ _ | _ = No  ?decEquiv

public export
Preorder Integer where
  LTE x y = (prim__lte_Integer x y = 1)

  decLTE x y with (prim__lte_Integer x y)
    decLTE _ _ | 1 = Yes Refl
    decLTE _ _ | _ = No  ?decLTE

  proofReflexivity  = believe_me ()
  proofTransitivity = believe_me ()

public export
Order Integer where
  LT x y = (prim__lt_Integer x y = 1)

  decLT x y with (prim__lt_Integer x y)
    decLT _ _ | 1 = Yes Refl
    decLT _ _ | _ = No  ?decLT
