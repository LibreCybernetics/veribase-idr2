module Data.Nat.Order

import Builtin

import Data.Bool
import public Data.Nat.Basic
import Data.Nat.Equiv
import Relation.Equiv
import Relation.Order

%default total

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
  proofOfReflexivity (S x) = proofOfReflexivity x

  proofOfTransitivity Z    Z     z  Refl Refl = Refl
  proofOfTransitivity Z (S y)    Z  Refl Refl impossible
  proofOfTransitivity Z (S y) (S z) Refl prf = Refl

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

  proofOfSoundness1    _     Z  Refl impossible
  proofOfSoundness1    Z  (S y) Refl = Refl
  proofOfSoundness1 (S x) (S y) prf  = ?orderSoundness1Hole

  proofOfSoundness2    _     Z  Refl impossible
  -- TODO: issue with not
  -- proofOfSoundness2    Z  (S y) Refl = IsNEQ Z (S y)
  -- proofOfSoundness2 (S x) (S y) Refl = ?orderSoundness2Hole

  proofOfAntisymetry    Z    Z  Refl  Refl = IsEQ Z Z
  proofOfAntisymetry    Z  (S y) Refl Refl impossible
  proofOfAntisymetry (S x)    Z  Refl Refl impossible
  proofOfAntisymetry (S x) (S y) prf1 prf2 = ?antisymetryHole
