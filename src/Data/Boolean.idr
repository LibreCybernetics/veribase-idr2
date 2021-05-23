module Data.Boolean

import Builtin

import Algebra.Equivalence

%default total

public export
data Boolean = False | True

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

not : Boolean -> Boolean
not False = True
not True  = False

proofNotInvolution : (a : Boolean) -> not (not a) = a
proofNotInvolution False = Refl
proofNotInvolution True  = Refl

disj : Boolean -> Boolean -> Boolean
disj False False = False
disj _     _     = True

proofDisjLeftAnnihilation : (a : Boolean) -> True `disj` a = True
proofDisjLeftAnnihilation False = Refl
proofDisjLeftAnnihilation True  = Refl

proofDisjRightAnnihilation : (a : Boolean) -> a `disj` True = True
proofDisjRightAnnihilation False = Refl
proofDisjRightAnnihilation True  = Refl

proofDisjLeftIdentity : (a : Boolean) -> False `disj` a = a
proofDisjLeftIdentity False = Refl
proofDisjLeftIdentity True  = Refl

proofDisjRightIdentity : (a : Boolean) -> a `disj` False = a
proofDisjRightIdentity False = Refl
proofDisjRightIdentity True  = Refl

proofDisjCommutative : (a, b : Boolean) -> a `disj` b = b `disj` a
proofDisjCommutative False b =
  rewrite proofDisjLeftIdentity b in
  rewrite proofDisjRightIdentity b in
  Refl
proofDisjCommutative True b = rewrite proofDisjRightAnnihilation b in Refl

proofDisjAssociative : (a, b, c : Boolean) -> a `disj` (b `disj` c) = (a `disj` b) `disj` c
proofDisjAssociative False b c =
  rewrite proofDisjLeftIdentity b in
  rewrite proofDisjLeftIdentity (b `disj` c) in
  Refl
proofDisjAssociative True b c = Refl

conj : Boolean -> Boolean -> Boolean
conj True True = True
conj _    _    = False

proofConjLeftAnnihilation : (a : Boolean) -> False `conj` a = False
proofConjLeftAnnihilation False = Refl
proofConjLeftAnnihilation True  = Refl

proofConjRightAnnihilation : (a : Boolean) -> a `conj` False = False
proofConjRightAnnihilation False = Refl
proofConjRightAnnihilation True  = Refl

proofConjLeftIdentity : (a : Boolean) -> True `conj` a = a
proofConjLeftIdentity False = Refl
proofConjLeftIdentity True  = Refl

proofConjRightIdentity : (a : Boolean) -> a `conj` True = a
proofConjRightIdentity False = Refl
proofConjRightIdentity True  = Refl

proofConjCommutative : (a, b : Boolean) -> a `conj` b = b `conj` a
proofConjCommutative False b = rewrite proofConjRightAnnihilation b in Refl
proofConjCommutative True b =
  rewrite proofConjLeftIdentity b in
  rewrite proofConjRightIdentity b in
  Refl

proofConjAssociative : (a, b, c : Boolean) -> a `conj` (b `conj` c) = (a `conj` b) `conj` c
proofConjAssociative False b c = Refl
proofConjAssociative True b c =
  rewrite proofConjLeftIdentity b in
  rewrite proofConjLeftIdentity (b `conj` c) in
  Refl

public export
decToBoolean : Dec t -> Boolean
decToBoolean (Yes _) = True
decToBoolean (No  _) = False
