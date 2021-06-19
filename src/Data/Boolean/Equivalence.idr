module Data.Boolean.Equivalence

import Builtin

import Algebra.Relation.Equivalence

import public Data.Boolean.Basic

%default total

public export
data BooleanEquiv : (a, b : Boolean) -> Type where
  BothFalse : BooleanEquiv False False
  BothTrue  : BooleanEquiv True  True

public export
Uninhabited (BooleanEquiv False True) where
  uninhabited BothFalse impossible
  uninhabited BothTrue  impossible

public export
Uninhabited (BooleanEquiv True False) where
  uninhabited BothFalse impossible
  uninhabited BothTrue  impossible

public export
Equivalence Boolean where
  Equiv = BooleanEquiv

  decEquiv False False = Yes BothFalse
  decEquiv True  True  = Yes BothTrue
  decEquiv False True  = No  absurd
  decEquiv True  False = No  absurd
