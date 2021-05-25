module Algebra.Magma

import Builtin

infixl 5 <>

public export
interface Magma t where
  (<>) : t -> t -> t
