module Algebra.Group.Group

import Builtin

import public Algebra.Group.Monoid

public export
interface Monoid t => Group t where
  neg : t -> t
  proofLeftInverse : (x : t) -> neg x <> x = Monoid.id
  proofRightInverse : (x : t) -> x <> neg x = Monoid.id
