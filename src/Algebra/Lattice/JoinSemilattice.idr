module Algebra.Lattice.JoinSemilattice

import Builtin

import Algebra.Relation.Preorder
import Algebra.Relation.Order

%default total

infixl 5 \/

public export
interface Order t => JoinSemilattice t where
  (\/) : t -> t -> t

  proofIdempotence : (x : t) -> x \/ x = x
  proofCommutative : (x, y : t) -> x \/ y = y \/ x
  proofAssociative : (x, y, z : t) -> x \/ (y \/ z) = (x \/ y) \/ z

  proofUpperBound : (x, y : t) -> (x `LTE` x \/ y, y `LTE` x \/ y)
  proofLeastUpperBound : (b, x, y : t) -> x `LTE` b -> y `LTE` b
                       ->  x \/ y `LTE` b
