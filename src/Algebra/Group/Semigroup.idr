module Algebra.Group.Semigroup

import Builtin

import public Algebra.Group.Magma

public export
interface Magma t => Semigroup t where
  proofAssociativity : (x, y, z : t) -> x <> (y <> z) = (x <> y) <> z
