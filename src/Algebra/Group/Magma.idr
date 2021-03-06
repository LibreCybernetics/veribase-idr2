module Algebra.Group.Magma

import Builtin

%default total

infixl 5 <>

public export
interface Magma t where
  (<>) : t -> t -> t

public export
interface Magma t => CommutativeMagma t where
  proofCommutative : (x, y : t) -> x <> y = y <> x
