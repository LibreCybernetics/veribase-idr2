module Algebra.Relation.Preorder

import public Builtin

%default total

public export
interface Preorder t where
  LTE : t -> t -> Type
  decLTE : (x, y : t) -> Dec (x `LTE` y)

  proofReflexivity : (x : t) -> x `LTE` x
  proofTransitivity : (x, y, z : t) -> x `LTE` y -> y `LTE` z -> x `LTE` z