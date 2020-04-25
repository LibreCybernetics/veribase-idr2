module Data.Nat

import Builtin

import Algebra.Group.Monoid
import Algebra.Group.Quasigroup

%default total

public export
data Nat = Z | S Nat

public export
[NatSumMagma] Magma Nat where
  x ⋄    Z  = x
  x ⋄ (S y) = S (x ⋄ y)

public export
[NatSumSemigroup] Semigroup Nat using NatSumMagma where
  proofOfAssociativity    x     y     Z  = Refl
  proofOfAssociativity    x     y  (S z) = rewrite proofOfAssociativity x y z in Refl
