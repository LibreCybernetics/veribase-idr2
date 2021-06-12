module Data.PrimInteger

import Builtin

import Algebra.Relation.Equivalence
import Algebra.Relation.Preorder
import Algebra.Relation.Order

import Control.Show

%default total

public export
Equivalence Integer where
  Equiv x y = (prim__eq_Integer x y = 1)

  decEquiv x y with (prim__eq_Integer x y)
    decEquiv _ _ | 1 = Yes Refl
    decEquiv _ _ | _ = No  ?decEquiv

public export
Preorder Integer where
  LTE x y = (prim__lte_Integer x y = 1)

  decLTE x y with (prim__lte_Integer x y)
    decLTE _ _ | 1 = Yes Refl
    decLTE _ _ | _ = No  ?decLTE

  proofReflexivity  = believe_me ()
  proofTransitivity = believe_me ()

public export
Order Integer where
  LT x y = (prim__lt_Integer x y = 1)

  decLT x y with (prim__lt_Integer x y)
    decLT _ _ | 1 = Yes Refl
    decLT _ _ | _ = No  ?decLT

public export
Show Integer where
  show = prim__cast_IntegerString

%integerLit fromPrimInteger

public export
interface SupportPrimIntegerLiteral t where
  PrimIntegerRestriction : Integer -> Type
  fromPrimInteger : (x : Integer) -> {auto ok : PrimIntegerRestriction x} -> t
  toPrimInteger : t -> Integer

public export
SupportPrimIntegerLiteral Integer where
  PrimIntegerRestriction x = Unit
  fromPrimInteger x = x
  toPrimInteger = identity
