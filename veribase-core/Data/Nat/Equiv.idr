module Data.Nat.Equiv

import Builtin

import public Data.Nat.Basic
import Relation.Equiv

%default total

public export
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
