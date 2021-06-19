module Data.Boolean.Order

import Builtin

import Algebra.Relation.Equivalence
import Algebra.Relation.Preorder
import Algebra.Relation.Order

import public Data.Boolean.Basic
import public Data.Boolean.Equivalence

%default total

public export
data BooleanLTE : (a, b : Boolean) -> Type where
  FalseLTEAny : BooleanLTE False b
  TrueLTETrue : BooleanLTE True  True

public export
Uninhabited (BooleanLTE True False) where
  uninhabited FalseLTEAny impossible
  uninhabited TrueLTETrue impossible

public export
Preorder Boolean where
  LTE = BooleanLTE

  decLTE False _     = Yes FalseLTEAny
  decLTE True  False = No  absurd
  decLTE True  True  = Yes TrueLTETrue

  proofReflexivity False = FalseLTEAny
  proofReflexivity True  = TrueLTETrue

  proofTransitivity False False _     FalseLTEAny FalseLTEAny = FalseLTEAny
  proofTransitivity False True  True  FalseLTEAny TrueLTETrue = FalseLTEAny
  proofTransitivity True  True  True  TrueLTETrue TrueLTETrue = TrueLTETrue
data BooleanLT : (a, b : Boolean) -> Type where
  FalseLTTrue : BooleanLT False True

public export
Uninhabited (BooleanLT False False) where
  uninhabited FalseLTTrue impossible

public export
Uninhabited (BooleanLT True _) where
  uninhabited FalseLTTrue impossible

public export
Order Boolean where
  LT = BooleanLT

  decLT False False = No  absurd
  decLT False True  = Yes FalseLTTrue
  decLT True  _     = No  absurd

  proofAntisymetry False False FalseLTEAny FalseLTEAny = BothFalse
  proofAntisymetry True  True  TrueLTETrue TrueLTETrue = BothTrue

  proofLTThenLTE FalseLTTrue = FalseLTEAny

  proofLTEThenLTOrEquiv False False FalseLTEAny = Right BothFalse
  proofLTEThenLTOrEquiv False True  FalseLTEAny = Left  FalseLTTrue
  proofLTEThenLTOrEquiv True  True  TrueLTETrue = Right BothTrue
