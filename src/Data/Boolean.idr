module Data.Boolean

import public Builtin

import public Algebra.Equivalence
import public Algebra.Monoid

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

public export
decToBoolean : Dec t -> Boolean
decToBoolean (Yes _) = True
decToBoolean (No  _) = False
