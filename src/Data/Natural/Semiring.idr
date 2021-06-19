module Data.Natural.Semiring

import Builtin

import Algebra.Group.Magma
import Algebra.Group.Semigroup
import Algebra.Group.Monoid

import Algebra.Ring.Semiring

import public Data.Natural.Basic
import public Data.Natural.Group

%default total

public export
Semiring Natural where
  (+) = add
  (*) = mult

  zero = Zero
  one  = (Succesor Zero)

  proofSumZero = proofRightIdentity @{NaturalSumMonoid}
  proofSumCommutative = proofCommutative @{NaturalSumCommutativeMagma}
  proofSumAssociative = proofAssociative @{NaturalSumSemigroup}

  proofMultOneLeft  = proofLeftIdentity  @{NaturalMultMonoid}
  proofMultOneRight = proofRightIdentity @{NaturalMultMonoid}
  proofMultAssociative = proofAssociative @{NaturalMultSemigroup}

  proofMultDistributesSumLeft  = proofMultLeftDistributesAdd
  proofMultDistributesSumRight = proofMultRightDistributesAdd

  zeroAnnihilatorLeft  = proofMultLeftAnnihilation
  zeroAnnihilatorRight = proofMultRightAnnihilation
