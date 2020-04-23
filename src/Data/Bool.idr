module Data.Bool

import Builtin

import Algebra.Group.Monoid
import Algebra.Group.Quasigroup

%default total

-- Value Level

public export
data Bool = False | True

-- Type Level

public export
data IsTrue : Bool → Type where
  ItIsTrue : IsTrue True

public export
data IsFalse : Bool → Type where
  ItIsFalse : IsFalse False

-- TODO: Move to complemented lattice interface
public export
not : Bool → Bool
not False = True
not True  = False

-- Disjunction Related Instances

[BoolDisjMagma] Magma Bool where
  False ⋄ False = False
  _     ⋄ _     = True

[BoolDisjCommutativeMagma] CommutativeMagma Bool using BoolDisjMagma where
  proofOfCommutativity False False = Refl
  proofOfCommutativity False True  = Refl
  proofOfCommutativity True  False = Refl
  proofOfCommutativity True  True  = Refl

[BoolDisjSemigroup] Semigroup Bool using BoolDisjMagma where
  proofOfAssociativity False y z = Refl
  proofOfAssociativity True  y z = Refl

[BoolDisjMonoid] Monoid Bool using BoolDisjSemigroup where
  e = False
  proofOfLeftIdentity  False = Refl
  proofOfLeftIdentity  True  = Refl
  proofOfRightIdentity False = Refl
  proofOfRightIdentity True  = Refl

-- Conjunction Related Instances

[BoolConjMagma] Magma Bool where
  True ⋄ True = True
  _    ⋄ _    = False

[BoolConjCommutativeMagma] CommutativeMagma Bool using BoolConjMagma where
  proofOfCommutativity False False = Refl
  proofOfCommutativity True  True  = Refl
  proofOfCommutativity True  False = Refl
  proofOfCommutativity True  True  = Refl

[BoolConjSemigroup] Semigroup Bool using BoolConjMagma where
  proofOfAssociativity False y z = Refl
  proofOfAssociativity True  y z = Refl

[BoolConjMonoid] Monoid Bool using BoolConjSemigroup where
  e = True
  proofOfLeftIdentity  True  = Refl
  proofOfLeftIdentity  False = Refl
  proofOfRightIdentity True  = Refl
  proofOfRightIdentity False = Refl

-- Material Implication Related Instances

[BoolImplMagma] Magma Bool where
  True ⋄ False = False
  _    ⋄ _     = True

-- XOR Related Instances

[BoolXorMagma] Magma Bool where
  False ⋄ False = False
  True  ⋄ True  = False
  _     ⋄ _     = True

[BoolXorQuasigroup] Quasigroup Bool using BoolXorMagma where
  proofOfLeftCancellative False False False Refl = Refl
  proofOfLeftCancellative False False True  Refl impossible
  proofOfLeftCancellative False True  False Refl impossible
  proofOfLeftCancellative False True  True  Refl = Refl
  proofOfLeftCancellative True  False False Refl = Refl
  proofOfLeftCancellative True  False True  Refl impossible
  proofOfLeftCancellative True  True  False Refl impossible
  proofOfLeftCancellative True  True  True  Refl = Refl
  proofOfRightCancellative False False False Refl = Refl
  proofOfRightCancellative False False True  Refl impossible
  proofOfRightCancellative False True  False Refl impossible
  proofOfRightCancellative False True  True  Refl = Refl
  proofOfRightCancellative True  False False Refl = Refl
  proofOfRightCancellative True  False True  Refl impossible
  proofOfRightCancellative True  True  False Refl impossible
  proofOfRightCancellative True  True  True  Refl = Refl
