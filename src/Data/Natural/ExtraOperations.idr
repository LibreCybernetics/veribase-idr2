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

export
proofDiffGTEThenMinus : (x, y : Natural) -> x `GTE` y -> diff x y = minus x y
proofDiffGTEThenMinus x Zero _ = case x of
  Zero          => Refl
  (Succesor x') => Refl
proofDiffGTEThenMinus (Succesor x) (Succesor y) (SuccesorLTE p) =
  rewrite proofDiffGTEThenMinus x y p in Refl


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
