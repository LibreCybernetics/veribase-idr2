module Data.Natural.ExtraOperations

import Builtin

import Algebra.Relation.Preorder

import public Data.Natural.Basic
import public Data.Natural.Order

%default total

public export
minus : (x, y : Natural) -> {auto ok : x `GTE` y} -> Natural
minus x Zero = x
minus (Succesor x) (Succesor y) {ok=(SuccesorLTE p)} = minus x y

public export
divRem : (x, y : Natural) -> {auto ok : NotZero y} -> (Natural, Natural)
divRem x y = case decLTE y x of
  Yes _ => let (d, r) := divRem (x `minus` y) y in (Succesor d, r)
  No  _ => (Zero, x)

public export
div : (x, y : Natural) -> {auto ok : NotZero y} -> Natural
div x y = fst $ divRem x y

public export
rem : (x, y : Natural) -> {auto ok : NotZero y} -> Natural
rem x y = snd $ divRem x y
