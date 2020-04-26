module Data.Nat.Order

import Builtin

import Data.Bool
import public Data.Nat.Basic
import Relation.Equiv
import Relation.Order

%default total


Preorder Nat where
  Z     ≤    _  = True
  (S x) ≤    Z  = False
  (S x) ≤ (S y) = x ≤ y

  proofOfReflexivity    Z  = Refl
  proofOfReflexivity (S x) = proofOfReflexivity x

  proofOfTransitivity Z    Z     z  Refl Refl = Refl
  proofOfTransitivity Z (S y)    Z  Refl Refl impossible
  proofOfTransitivity Z (S y) (S z) Refl prf = Refl
