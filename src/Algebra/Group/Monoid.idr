module Algebra.Group.Monoid

import Builtin

import Algebra.Group.Magma
import Algebra.Group.Semigroup

%default total

public export
interface Semigroup t => Monoid t where
  id : t
  proofLeftIdentity : (x : t) -> id <> x = x
  proofRightIdentity : (x : t) -> x <> id = x
