module Data.Nat

import Builtin

import Algebra.Group.Monoid
import Algebra.Group.Quasigroup
import Algebra.Ring.Ring
import Data.Bool
import Data.Integer
import Data.Integral
import Relation.Equiv
import Relation.Order

%builtinNatZero Z
%builtinNatSucc S

public export
data Nat = Z | S Nat

eq : Nat → Nat → Bool
eq    Z     Z  = True
eq    Z  (S _) = False
eq (S _)    Z  = False
eq (S x) (S y) = eq x y

--
-- Relation
--

public export
Equiv Nat where
  (≡) = eq

  proofOfSoundness1 = ?proofOfSoundness1
  proofOfSoundness2 = ?proofOfSoundness2

  proofOfReflexivity    Z  = Refl
  proofOfReflexivity (S x) = ?reflexivityEquivNameClash

  proofOfSymetry    Z     Z  Refl = Refl
  proofOfSymetry    Z  (S _) Refl impossible
  proofOfSymetry (S _)    Z  Refl impossible
  proofOfSymetry (S x) (S y) prf  = rewrite proofOfSymetry x y prf in Refl
  proofOfTransitivity = ?proofOfTransitivity

public export
Preorder Nat where
  Z     ≤    _  = True
  (S _) ≤    Z  = False
  (S x) ≤ (S y) = x ≤ y

  proofOfSoundness1    Z     _  Refl = rewrite notTrueIsFalse in Refl
  proofOfSoundness1 (S x)    Z  Refl impossible
  proofOfSoundness1 (S x) (S y) prf  = ?preorderSoundness1Hole

  proofOfSoundness2 = ?preorderSoundness2Hole

  proofOfReflexivity    Z  = Refl
  proofOfReflexivity (S x) = ?reflexivityPreorderNameClash

  proofOfTransitivity Z    Z     z  Refl Refl = Refl
  proofOfTransitivity Z (S y)    Z  Refl Refl impossible
  proofOfTransitivity Z (S y) (S z) Refl prf = Refl

public export
TotalPreorder Nat where
  proofOfTotality    Z   _ = Left Refl
  proofOfTotality (S x)  Z = Right Refl
  proofOfTotality (S x) (S y) with ((S x) ≤ (S y))
  -- proofOfTotality (S x) (S y) | False = Right Refl -- TODO: flip proof
  proofOfTotality (S x) (S y) | True  = Left Refl

public export
Order Nat where
  _     <    Z  = False
  Z     < (S _) = True
  (S x) < (S y) = x < y

public export
TotalOrder Nat where

public export
StrictOrder Nat where

public export
StrictTotalOrder Nat where

--
-- Operations
--

-- Addition

%builtinNatAdd add

add : Nat → Nat → Nat
add x    Z  = x
add x (S y) = S (x `add` y)

public export
[NatSumMagma] Magma Nat where
  (⋄) = add

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

%builtinNatMul mul

mul : Nat → Nat → Nat
mul x    Z  = Z
mul x (S y) = x `add` (x `mul` y)

public export
[NatProdMagma] Magma Nat where
  (⋄) = mul

public export
[NatProdCommutativeMagma] CommutativeMagma Nat using NatProdMagma where
  proofOfCommutativity Z Z = Refl

public export
[NatProdSemigroup] Semigroup Nat using NatProdMagma where
  proofOfAssociativity Z Z Z = Refl

public export
[NatProdMonoid] Monoid Nat using NatProdSemigroup where
  e = S Z

  proofOfLeftIdentity  Z = Refl
  proofOfRightIdentity Z = Refl

-- Joining Addition/Multiplication in a Semiring

public export
Semiring Nat where
  (+) = (⋄) @{NatSumMagma}
  (⋅) = (⋄) @{NatProdMagma}
  zero = Z
  one = S Z

-- limited minus

%builtinNatSub minus

public export
minus : (x, y: Nat) → {auto ok: x `GTE` y} → Nat
minus    x     Z       = x
minus    Z  (S _)      = Z
minus (S x) (S y) {ok} = minus x y {ok = ?predOfOrder ok}

-- Integral

%builtinNatDiv div
%builtinNatMod mod

div : Nat → Nat → Nat
div _ Z = Z
div Z _ = Z
div n d with (n `isGTE` d)
  div n d | No  _    = Z
  div n d | Yes prf  = S $ (minus n d {ok = prf}) `div` d

mod : Nat → Nat → Nat
mod _ Z = Z
mod Z _ = Z
mod n d with (n `isGTE` d)
  mod n d | No  _   = n
  mod n d | Yes prf = (minus n d {ok = prf}) `mod` d

public export
Integral Nat where
  fromInteger x = if x ≤ 0
    then Z
    else S (fromInteger (x - 1))
  divMod n d = (n `div` d, n `mod` d)

