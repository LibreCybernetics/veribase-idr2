module Data.Nat.Semiring

import Builtin

import Algebra.Group.Monoid
import Algebra.Group.Loop
import Algebra.Ring.Semiring
import public Data.Nat.Basic

%default total

-- Sum

public export
[NatSumMagma] Magma Nat where
  x ⋄    Z  = x
  x ⋄ (S y) = S (x ⋄ y)

public export
[NatSumCommutativeMagma] CommutativeMagma Nat using NatSumMagma where
  proofOfCommutativity    Z     Z  = Refl
  proofOfCommutativity    Z  (S y) = rewrite proofOfCommutativity Z y in Refl
  proofOfCommutativity (S x)    Z  = rewrite proofOfCommutativity Z x in Refl
  proofOfCommutativity (S x) (S y) =
    rewrite proofOfCommutativity (S y) x in
    rewrite proofOfCommutativity (S x) y in
    rewrite proofOfCommutativity x y in Refl

public export
[NatSumSemigroup] Semigroup Nat using NatSumMagma where
  proofOfAssociativity    x     y     Z  = Refl
  proofOfAssociativity    x     y  (S z) = rewrite proofOfAssociativity x y z in Refl

public export
[NatSumMonoid] Monoid Nat using NatSumSemigroup where
  e = Z
  proofOfLeftIdentity    Z  = Refl
  proofOfLeftIdentity (S x) = rewrite proofOfLeftIdentity @{NatSumMonoid} x in Refl
  proofOfRightIdentity   x  = Refl

public export
[NatSumQuasigroup] Quasigroup Nat using NatSumMagma NatSumMonoid where
  proofOfLeftCancellative x    Z     Z  Refl = Refl
  proofOfLeftCancellative Z    Z  (S z) Refl impossible
  proofOfLeftCancellative Z (S y)    Z  Refl impossible
  -- TODO: Same issue as Semigroup a ⇒ Monoid (Maybe a)
  -- proofOfLeftCancellative Z (S y) (S z) prf =
  --  rewrite proofOfLeftCancellative Z y z prf in ?hole
  -- TODO: Requires some other order proofs
  --proofOfLeftCancellative (S x) Z (S z) Refl = absurd

  proofOfRightCancellative Z Z Z Refl = Refl
  -- TODO: Remainder

public export
[NatSumCommutativeSemigroup] CommutativeSemigroup Nat using NatSumCommutativeMagma NatSumSemigroup where

public export
[NatSumCommutativeMonoid] CommutativeMonoid Nat using NatSumCommutativeSemigroup NatSumMonoid where

-- Product

public export
[NatProdMagma] Magma Nat where
  x ⋄    Z  = Z
  x ⋄ (S y) = (⋄) @{NatSumMagma} x (x ⋄ y)

public export
[NatProdCommutativeMagma] CommutativeMagma Nat using NatProdMagma where

public export
[NatProdSemigroup] Semigroup Nat using NatProdMagma where

public export
[NatProdMonoid] Monoid Nat using NatProdSemigroup where

-- Semiring

public export
Semiring Nat where
  (+) = (⋄) @{NatSumMagma}
  (⋅) = (⋄) @{NatProdMagma}
  zero = Z
  one = S Z
