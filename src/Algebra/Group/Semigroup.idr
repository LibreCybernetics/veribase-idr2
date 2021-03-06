module Algebra.Group.Semigroup

import Builtin

import Algebra.Group.Magma

%default total

public export
interface Magma t => Semigroup t where
  proofAssociative : (x, y, z : t) -> x <> (y <> z) = (x <> y) <> z

public export
interface (CommutativeMagma t, Semigroup t) => CommutativeSemigroup t where

public export
CommutativeMagma t => Semigroup t => CommutativeSemigroup t where
