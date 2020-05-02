module Data.Integer

import Builtin

import Algebra.Ring.Ring
import Data.Integral
import Relation.Equiv
import Relation.Order

public export
Equiv Integer where
  x ≡ y = primBoolToBool $ prim__eq_Integer x y

public export
Preorder Integer where
  x ≤ y = primBoolToBool $ prim__lte_Integer x y

public export
TotalPreorder Integer where

public export
Order Integer where
  x < y = primBoolToBool $ prim__lt_Integer x y

public export
TotalOrder Integer where

public export
StrictOrder Integer where

public export
StrictTotalOrder Integer where

public export
Semiring Integer where
  (+) = prim__add_Integer
  (⋅) = prim__mul_Integer

public export
Integral Integer where
  fromInteger = id
  x `divMod` y = (prim__div_Integer x y, prim__mod_Integer x y)

public export
Ring Integer where
  sumInv = prim__sub_Integer 0
