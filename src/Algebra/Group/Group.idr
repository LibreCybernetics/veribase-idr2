module Algebra.Group.Group

import Builtin

import Algebra.Group.Magma
import Algebra.Group.Monoid
import Algebra.Group.Semigroup

%default total

public export
interface Monoid t => Group t where
  neg : t -> t
  proofLeftInverse : (x : t) -> neg x <> x = Monoid.id
  proofRightInverse : (x : t) -> x <> neg x = Monoid.id
