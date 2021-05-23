module Algebra.Equivalence

import Builtin

%default total

public export
interface Equivalence t where
  Equiv : (a, b : t) -> Type
  decEquiv : (a, b : t) -> Dec (Equiv a b)
