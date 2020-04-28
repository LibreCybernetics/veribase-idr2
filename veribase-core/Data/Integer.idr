module Data.Integer

import Builtin

import Algebra.Ring.Ring
import Relation.Preorder

public export
Preorder Integer where
  x ≤ y = primBoolToBool $ prim__lte_Integer x y

public export
Semiring Integer where
  (+) = prim__add_Integer
  (⋅) = prim__mul_Integer

public export
Ring Integer where
  sumInv = prim__sub_Integer 0
