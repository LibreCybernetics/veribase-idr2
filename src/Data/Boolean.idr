module Data.Boolean

import public Builtin

import public Algebra.Relation.Equivalence
import public Algebra.Relation.Preorder
import public Algebra.Relation.Order

import public Algebra.Group.Monoid

import public Algebra.Lattice.JoinSemilattice
import public Algebra.Lattice.MeetSemilattice

import Data.Either

%default total

--
-- Values
--

public export
data Boolean = False | True

--
-- Relation
--

data BooleanEquiv : (a, b : Boolean) -> Type where
  BothFalse : BooleanEquiv False False
  BothTrue  : BooleanEquiv True  True

public export
Uninhabited (BooleanEquiv False True) where
  uninhabited BothFalse impossible
  uninhabited BothTrue  impossible

public export
Uninhabited (BooleanEquiv True False) where
  uninhabited BothFalse impossible
  uninhabited BothTrue  impossible

public export
Equivalence Boolean where
  Equiv = BooleanEquiv

  decEquiv False False = Yes $ BothFalse
  decEquiv True  True  = Yes $ BothTrue
  decEquiv False True  = No  $ absurd
  decEquiv True  False = No  $ absurd

data BooleanLTE : (a, b : Boolean) -> Type where
  FalseLTEAny : BooleanLTE False b
  TrueLTETrue : BooleanLTE True True

public export
Uninhabited (BooleanLTE True False) where
  uninhabited FalseLTEAny impossible
  uninhabited TrueLTETrue impossible

public export
Preorder Boolean where
  LTE = BooleanLTE

  decLTE False _     = Yes FalseLTEAny
  decLTE True  False = No absurd
  decLTE True  True  = Yes TrueLTETrue

  proofReflexivity False = FalseLTEAny
  proofReflexivity True  = TrueLTETrue

  proofTransitivity False False _     FalseLTEAny FalseLTEAny = FalseLTEAny
  proofTransitivity False True  True  FalseLTEAny TrueLTETrue = FalseLTEAny
  proofTransitivity True  True  True  TrueLTETrue TrueLTETrue = TrueLTETrue

data BooleanLT : (a, b : Boolean) -> Type where
  FalseLTTrue : BooleanLT False True

public export
Uninhabited (BooleanLT False False) where
  uninhabited FalseLTTrue impossible

public export
Uninhabited (BooleanLT True _) where
  uninhabited FalseLTTrue impossible

public export
Order Boolean where
  LT = BooleanLT

  decLT False False = No absurd
  decLT False True  = Yes FalseLTTrue
  decLT True  _     = No absurd

  proofAntisymetry False False FalseLTEAny FalseLTEAny = BothFalse
  proofAntisymetry True  True  TrueLTETrue TrueLTETrue = BothTrue

  proofLTThenLTE FalseLTTrue = FalseLTEAny

  proofLTEThenLTOrEquiv False False FalseLTEAny = Right BothFalse
  proofLTEThenLTOrEquiv False True  FalseLTEAny = Left  FalseLTTrue
  proofLTEThenLTOrEquiv True  True  TrueLTETrue = Right BothTrue

--
-- Operations
--

not : Boolean -> Boolean
not False = True
not True  = False

proofNotInvolution : (a : Boolean) -> not (not a) = a
proofNotInvolution False = Refl
proofNotInvolution True  = Refl

public export
[BooleanDisjMagma] Magma Boolean where
  False <> False = False
  _     <> _     = True

public export
disj : Boolean -> Boolean -> Boolean
disj = (<>) @{BooleanDisjMagma}

proofDisjLeftIdentity : (a : Boolean) -> False `disj` a = a
proofDisjLeftIdentity False = Refl
proofDisjLeftIdentity True  = Refl

proofDisjRightIdentity : (a : Boolean) -> a `disj` False = a
proofDisjRightIdentity False = Refl
proofDisjRightIdentity True  = Refl

proofDisjLeftAnnihilation : (a : Boolean) -> True `disj` a = True
proofDisjLeftAnnihilation False = Refl
proofDisjLeftAnnihilation True  = Refl

proofDisjRightAnnihilation : (a : Boolean) -> a `disj` True = True
proofDisjRightAnnihilation False = Refl
proofDisjRightAnnihilation True  = Refl

public export
[BooleanDisjSemigroup] Semigroup Boolean using BooleanDisjMagma where
  proofAssociativity False b c =
    rewrite proofDisjLeftIdentity b in
    rewrite proofDisjLeftIdentity (b `disj` c) in
    Refl
  proofAssociativity True b c = Refl

public export
[BooleanDisjMonoid] Monoid Boolean using BooleanDisjSemigroup where
  id = False
  proofLeftIdentity = proofDisjLeftIdentity
  proofRightIdentity = proofDisjRightIdentity

proofDisjCommutative : (a, b : Boolean) -> a `disj` b = b `disj` a
proofDisjCommutative False b =
  rewrite proofDisjLeftIdentity b in
  rewrite proofDisjRightIdentity b in
  Refl
proofDisjCommutative True b = rewrite proofDisjRightAnnihilation b in Refl

public export
[BooleanConjMagma] Magma Boolean where
  True <> True = True
  _    <> _    = False

public export
conj : Boolean -> Boolean -> Boolean
conj = (<>) @{BooleanConjMagma}

proofConjLeftIdentity : (a : Boolean) -> True `conj` a = a
proofConjLeftIdentity False = Refl
proofConjLeftIdentity True  = Refl

proofConjRightIdentity : (a : Boolean) -> a `conj` True = a
proofConjRightIdentity False = Refl
proofConjRightIdentity True  = Refl

proofConjLeftAnnihilation : (a : Boolean) -> False `conj` a = False
proofConjLeftAnnihilation False = Refl
proofConjLeftAnnihilation True  = Refl

proofConjRightAnnihilation : (a : Boolean) -> a `conj` False = False
proofConjRightAnnihilation False = Refl
proofConjRightAnnihilation True  = Refl

public export
[BooleanConjSemigroup] Semigroup Boolean using BooleanConjMagma where
  proofAssociativity False b c = Refl
  proofAssociativity True b c =
    rewrite proofConjLeftIdentity b in
    rewrite proofConjLeftIdentity (b `conj` c) in
    Refl

public export
[BooleanConjMonoid] Monoid Boolean using BooleanConjSemigroup where
  id = True
  proofLeftIdentity  = proofConjLeftIdentity
  proofRightIdentity = proofConjRightIdentity

proofConjCommutative : (a, b : Boolean) -> a `conj` b = b `conj` a
proofConjCommutative False b = rewrite proofConjRightAnnihilation b in Refl
proofConjCommutative True b =
  rewrite proofConjLeftIdentity b in
  rewrite proofConjRightIdentity b in
  Refl

--
-- Lattice
--

public export
MeetSemilattice Boolean where
  (/\) = conj

  proofIdempotence False = Refl
  proofIdempotence True  = Refl
  proofAssociative = proofAssociativity @{BooleanConjSemigroup}
  proofCommutative = proofConjCommutative

  proofLowerBound False False = (FalseLTEAny, FalseLTEAny)
  proofLowerBound False True  = (FalseLTEAny, FalseLTEAny)
  proofLowerBound True  False = (FalseLTEAny, FalseLTEAny)
  proofLowerBound True  True  = (TrueLTETrue, TrueLTETrue)

  proofGreatestLowerBound False False False FalseLTEAny FalseLTEAny = FalseLTEAny
  proofGreatestLowerBound False False True  FalseLTEAny FalseLTEAny = FalseLTEAny
  proofGreatestLowerBound False True  False FalseLTEAny FalseLTEAny = FalseLTEAny
  proofGreatestLowerBound False True  True  FalseLTEAny FalseLTEAny = FalseLTEAny
  proofGreatestLowerBound True  True  True  TrueLTETrue TrueLTETrue = TrueLTETrue

public export
JoinSemilattice Boolean where
  (\/) = disj

  proofIdempotence False = Refl
  proofIdempotence True  = Refl
  proofAssociative = proofAssociativity @{BooleanDisjSemigroup}
  proofCommutative = proofDisjCommutative

  proofUpperBound False False = (FalseLTEAny, FalseLTEAny)
  proofUpperBound False True  = (FalseLTEAny, TrueLTETrue)
  proofUpperBound True  False = (TrueLTETrue, FalseLTEAny)
  proofUpperBound True  True  = (TrueLTETrue, TrueLTETrue)

  proofLeastUpperBound False False False FalseLTEAny FalseLTEAny = FalseLTEAny
  proofLeastUpperBound True  False False FalseLTEAny FalseLTEAny = FalseLTEAny
  proofLeastUpperBound True  False True  FalseLTEAny TrueLTETrue = TrueLTETrue
  proofLeastUpperBound True  True  False TrueLTETrue FalseLTEAny = TrueLTETrue
  proofLeastUpperBound True  True  True  TrueLTETrue TrueLTETrue = TrueLTETrue

--
-- Util
--

public export
decToBoolean : Dec t -> Boolean
decToBoolean (Yes _) = True
decToBoolean (No  _) = False
