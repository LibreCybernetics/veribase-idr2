module Algebra.Relation.Order

import public Builtin

import public Algebra.Relation.Preorder
import public Algebra.Relation.Equivalence

import Data.Either

public export
interface (Equivalence t, Preorder t) => Order t where
  LT : t -> t -> Type
  decLT : (x, y : t) -> Dec (x `LT` y)

  proofAntisymetry : (x, y : t) -> x `LTE` y -> y `LTE` x -> x `Equiv` y
  proofLTThenLTE : {x, y : t} -> x `LT` y -> x `LTE` y
  proofLTEThenLTOrEquiv : {x, y : t} -> x `LTE` y -> Either (x `LT` y) (x `Equiv` y)
