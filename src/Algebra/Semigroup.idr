module Algebra.Semigroup

import Builtin

import public Algebra.Magma

public export
interface Magma t => Semigroup t where
  proofAssociativity : (x, y, z : t) -> x <> (y <> z) = (x <> y) <> z
