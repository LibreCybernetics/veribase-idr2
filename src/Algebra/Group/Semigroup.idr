module Algebra.Group.Semigroup

import Builtin

import Algebra.Group.Magma

%default total

public export
interface Magma t => Semigroup t where
  proofAssociativity : (x, y, z : t) -> x <> (y <> z) = (x <> y) <> z
