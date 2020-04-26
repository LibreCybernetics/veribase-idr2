module Data.Nat.Order

import Builtin

import Data.Bool
import public Data.Nat.Basic
import Data.Nat.Equiv
import Relation.Equiv
import Relation.Order

%default total

Preorder Nat where
  Z     ≤    _  = True
  (S _) ≤    Z  = False
  (S x) ≤ (S y) = x ≤ y

  proofOfReflexivity    Z  = Refl
  proofOfReflexivity (S x) = proofOfReflexivity x

  proofOfTransitivity Z    Z     z  Refl Refl = Refl
  proofOfTransitivity Z (S y)    Z  Refl Refl impossible
  proofOfTransitivity Z (S y) (S z) Refl prf = Refl

TotalPreorder Nat where
  proofOfTotality    Z   _ = Left Refl
  proofOfTotality (S x)  Z = Right Refl
  proofOfTotality (S x) (S y) with ((S x) ≤ (S y))
    -- proofOfTotality (S x) (S y) | False = Right Refl
    proofOfTotality (S x) (S y) | True  = Left Refl

Order Nat where
  _     <    Z  = False
  Z     < (S _) = True
  (S x) < (S y) = x < y

  proofOfAntisymetry    Z    Z  Refl  Refl = IsEQ Z Z
  proofOfAntisymetry    Z  (S y) Refl Refl impossible
  proofOfAntisymetry (S x)    Z  Refl Refl impossible
  proofOfAntisymetry (S x) (S y) prf1 prf2 = ?antisymetryHole
