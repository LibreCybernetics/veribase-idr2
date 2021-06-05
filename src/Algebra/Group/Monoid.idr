module Algebra.Group.Monoid

import Builtin

import public Algebra.Group.Semigroup

public export
interface Semigroup t => Monoid t where
  id : t
  proofLeftIdentity : (x : t) -> id <> x = x
  proofRightIdentity : (x : t) -> x <> id = x
