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

public export
Uninhabited (False = True) where
  uninhabited Refl impossible

public export
Uninhabited (True = False) where
  uninhabited Refl impossible

-- Don't use this externally, use the negation/complement of BooleanAlgebra
export %inline
not : Bool -> Bool
not False = True
not True  = False

export
notFalseIsTrue : not False = True
notFalseIsTrue = Refl

export
notTrueIsFalse : not True = False
notTrueIsFalse = Refl

-- Disjunction Related Instances

public export
[BoolDisjMagma] Magma Bool where
  False ⋄ False = False
  _     ⋄ _     = True

public export
[BoolDisjCommutativeMagma] CommutativeMagma Bool using BoolDisjMagma where
  proofOfCommutativity False False = Refl
  proofOfCommutativity False True  = Refl
  proofOfCommutativity True  False = Refl
  proofOfCommutativity True  True  = Refl

public export
[BoolDisjSemigroup] Semigroup Bool using BoolDisjMagma where
  proofOfAssociativity False y z = Refl
  proofOfAssociativity True  y z = Refl

public export
[BoolDisjMonoid] Monoid Bool using BoolDisjSemigroup where
  e = False
  proofOfLeftIdentity  False = Refl
  proofOfLeftIdentity  True  = Refl
  proofOfRightIdentity False = Refl
  proofOfRightIdentity True  = Refl

-- Conjunction Related Instances

public export
[BoolConjMagma] Magma Bool where
  True ⋄ True = True
  _    ⋄ _    = False

public export
[BoolConjCommutativeMagma] CommutativeMagma Bool using BoolConjMagma where
  proofOfCommutativity False False = Refl
  proofOfCommutativity True  True  = Refl
  proofOfCommutativity True  False = Refl
  proofOfCommutativity True  True  = Refl

public export
[BoolConjSemigroup] Semigroup Bool using BoolConjMagma where
  proofOfAssociativity False y z = Refl
  proofOfAssociativity True  y z = Refl

public export
[BoolConjMonoid] Monoid Bool using BoolConjSemigroup where
  e = True
  proofOfLeftIdentity  True  = Refl
  proofOfLeftIdentity  False = Refl
  proofOfRightIdentity True  = Refl
  proofOfRightIdentity False = Refl

-- Material Implication Related Instances

public export
[BoolImplMagma] Magma Bool where
  True ⋄ False = False
  _    ⋄ _     = True


public export
[BoolEquivMagma] Magma Bool where
  False ⋄ False = True
  True  ⋄ True  = True
  _     ⋄ _     = False

public export
[BoolEquivCommutativeMagma] CommutativeMagma Bool using BoolEquivMagma where
  proofOfCommutativity False False = Refl
  proofOfCommutativity False True  = Refl
  proofOfCommutativity True  False = Refl
  proofOfCommutativity True  True  = Refl

public export
[BoolEquivSemigroup] Semigroup Bool using BoolEquivMagma where
   proofOfAssociativity False False False = Refl
   proofOfAssociativity False False True  = Refl
   proofOfAssociativity False True  False = Refl
   proofOfAssociativity False True  True  = Refl
   proofOfAssociativity True  False False = Refl
   proofOfAssociativity True  False True  = Refl
   proofOfAssociativity True  True  False = Refl
   proofOfAssociativity True  True  True  = Refl

public export
[BoolXorMagma] Magma Bool where
  False ⋄ False = False
  True  ⋄ True  = False
  _     ⋄ _     = True

public export
[BoolXorCommutativeMagma] CommutativeMagma Bool using BoolXorMagma where
  proofOfCommutativity False False = Refl
  proofOfCommutativity False True  = Refl
  proofOfCommutativity True  False = Refl
  proofOfCommutativity True  True  = Refl

public export
[BoolXorSemigroup] Semigroup Bool using BoolXorMagma where
  proofOfAssociativity False False False = Refl
  proofOfAssociativity False False True  = Refl
  proofOfAssociativity False True  False = Refl
  proofOfAssociativity False True  True  = Refl
  proofOfAssociativity True  False False = Refl
  proofOfAssociativity True  False True  = Refl
  proofOfAssociativity True  True  False = Refl
  proofOfAssociativity True  True  True  = Refl

public export
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
