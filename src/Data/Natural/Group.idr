module Data.Natural.Group

import Builtin

import Algebra.Group.Magma
import Algebra.Group.Semigroup
import Algebra.Group.Monoid

import public Data.Natural.Basic

public export
[NaturalSumMagma] Magma Natural where
  (<>) = add

public export
[NaturalSumCommutativeMagma] CommutativeMagma Natural using NaturalSumMagma where
  proofCommutative = proofAddCommutative

public export
[NaturalSumSemigroup] Semigroup Natural using NaturalSumMagma where
  proofAssociative = proofAddAssociative

public export
[NaturalSumCommutativeSemigroup] CommutativeSemigroup Natural using NaturalSumCommutativeMagma NaturalSumSemigroup where

public export
[NaturalSumMonoid] Monoid Natural using NaturalSumSemigroup where
  id = Zero

  proofLeftIdentity = proofAddLeftIdentity
  proofRightIdentity _ = Refl

public export
[NaturalSumCommutativeMonoid] CommutativeMonoid Natural using NaturalSumCommutativeSemigroup NaturalSumMonoid where

public export
[NaturalMultMagma] Magma Natural where
  (<>) = mult

public export
[NaturalMultSemigroup] Semigroup Natural using NaturalMultMagma where
  proofAssociative x y Zero = Refl
  proofAssociative x y (Succesor z) =
    rewrite proofMultLeftDistributesAdd x y (mult y z) in
    rewrite proofAssociative x y z in
    Refl

public export
[NaturalMultMonoid] Monoid Natural using NaturalMultSemigroup where
  id = Succesor Zero

  proofLeftIdentity = proofMultLeftIdentity
  proofRightIdentity _ = Refl
