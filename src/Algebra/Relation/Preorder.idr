module Algebra.Relation.Preorder

import Builtin

%default total

public export
interface Preorder t where
  LTE : t -> t -> Type
  decLTE : (x, y : t) -> Dec (x `LTE` y)

  proofReflexivity : (x : t) -> x `LTE` x
  proofTransitivity : (x, y, z : t) -> x `LTE` y -> y `LTE` z -> x `LTE` z

public export
GTE : Preorder t => t -> t -> Type
GTE = flip LTE

public export
decGTE : Preorder t => (x, y : t) -> Dec (y `LTE` x)
decGTE x y = decLTE y x

public export
max : Preorder t => t -> t -> t
max x y = case decLTE x y of
  (Yes _) => y
  (No  _) => x

public export
min : Preorder t => t -> t -> t
min x y = case decLTE x y of
  (Yes _) => y
  (No  _) => x
