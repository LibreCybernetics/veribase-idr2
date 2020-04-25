module Data.Nat

import Builtin

import Algebra.Group.Monoid
import Algebra.Group.Quasigroup
import Data.Bool
import Relation.Equiv

%default total

public export
data Nat = Z | S Nat

-- Equiv

Equiv Nat where
  Z     ≡    Z  = True
  Z     ≡ (S _) = False
  (S _) ≡    Z  = False
  (S x) ≡ (S y) = x ≡ y

  proofOfReflexivity    Z  = Refl
  proofOfReflexivity (S x) = rewrite proofOfReflexivity x in Refl

  proofOfSymetry    Z     Z  Refl = Refl
  proofOfSymetry    Z  (S y) Refl impossible
  proofOfSymetry (S x)    Z  Refl impossible
  proofOfSymetry (S x) (S y) prf  = rewrite proofOfSymetry x y prf in Refl

  proofOfTransitivity    Z     Z     Z  Refl Refl = Refl
  proofOfTransitivity    Z     Z  (S z) Refl Refl impossible
  proofOfTransitivity    Z  (S y)    z  Refl Refl impossible
  proofOfTransitivity (S x)    Z     z  Refl Refl impossible
  proofOfTransitivity (S x) (S y)    Z  Refl Refl impossible
  proofOfTransitivity (S x) (S y) (S z) prf1 prf2 =
    rewrite proofOfTransitivity x y z prf1 prf2 in Refl

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
  proofOfLeftIdentity (S x) = rewrite proofOfLeftIdentity x in Refl
  proofOfRightIdentity x = Refl

public export
[NatSumCommutativeSemigroup] CommutativeSemigroup Nat using NatSumCommutativeMagma NatSumSemigroup where

public export
[NatSumCommutativeMonoid] CommutativeMonoid Nat using NatSumCommutativeSemigroup NatSumMonoid where
