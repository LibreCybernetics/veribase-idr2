module Data.Boolean.Lattice

import Builtin

import Algebra.Group.Magma
import Algebra.Group.Semigroup

import Algebra.Lattice.MeetSemilattice
import Algebra.Lattice.JoinSemilattice

import Algebra.Relation.Preorder
import Algebra.Relation.Order

import public Data.Boolean.Basic

import public Data.Boolean.Order
import public Data.Boolean.Group

%default total

public export
JoinSemilattice Boolean where
  (\/) = disj

  proofIdempotence False = Refl
  proofIdempotence True  = Refl

  proofAssociative = proofAssociative @{BooleanDisjSemigroup}
  proofCommutative = proofDisjCommutative

  proofUpperBound False False = (FalseLTEAny, FalseLTEAny)
  proofUpperBound False True  = (FalseLTEAny, TrueLTETrue)
  proofUpperBound True  False = (TrueLTETrue, FalseLTEAny)
  proofUpperBound True  True  = (TrueLTETrue, TrueLTETrue)

  proofLeastUpperBound False False False FalseLTEAny FalseLTEAny = FalseLTEAny
  proofLeastUpperBound True  False False FalseLTEAny FalseLTEAny = FalseLTEAny
  proofLeastUpperBound True  False True  FalseLTEAny TrueLTETrue = TrueLTETrue
  proofLeastUpperBound True  True  False TrueLTETrue FalseLTEAny = TrueLTETrue
  proofLeastUpperBound True  True  True  TrueLTETrue TrueLTETrue = TrueLTETrue

public export
MeetSemilattice Boolean where
  (/\) = conj

  proofIdempotence False = Refl
  proofIdempotence True  = Refl

  proofAssociative = proofAssociative @{BooleanConjSemigroup}
  proofCommutative = proofConjCommutative

  proofLowerBound False False = (FalseLTEAny, FalseLTEAny)
  proofLowerBound False True  = (FalseLTEAny, FalseLTEAny)
  proofLowerBound True  False = (FalseLTEAny, FalseLTEAny)
  proofLowerBound True  True  = (TrueLTETrue, TrueLTETrue)

  proofGreatestLowerBound False y     z     FalseLTEAny FalseLTEAny = FalseLTEAny
  proofGreatestLowerBound True  True  True  TrueLTETrue TrueLTETrue = TrueLTETrue
