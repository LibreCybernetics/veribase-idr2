module Algebra.Relation.Order

import Builtin

import Algebra.Relation.Preorder
import Algebra.Relation.Equivalence

import public Data.Either

%default total

public export
interface (Equivalence t, Preorder t) => Order t where
  LT : t -> t -> Type
  decLT : (x, y : t) -> Dec (x `LT` y)

  proofAntisymetry : (x, y : t) -> x `LTE` y -> y `LTE` x -> x `Equiv` y
  proofLTThenLTE : {x, y : t} -> x `LT` y -> x `LTE` y
  proofLTEThenLTOrEquiv : (x, y : t) -> x `LTE` y
                        -> Either (x `LT` y) (x `Equiv` y)

public export
GT : Order t => t -> t -> Type
GT = flip LT

public export
decGT : Order t => (x, y : t) -> Dec (y `LT` x)
decGT x y = decLT y x
