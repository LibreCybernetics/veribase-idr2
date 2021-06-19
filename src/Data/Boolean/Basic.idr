module Data.Boolean.Basic

import Builtin

%default total

public export
data Boolean = False | True

--
-- Negation / Complement
--

public export
not : Boolean -> Boolean
not False = True
not True  = False

export
proofNotInvolution : (a : Boolean) -> not (not a) = a
proofNotInvolution False = Refl
proofNotInvolution True  = Refl

--
-- Disjunction / Inclusive OR
--

public export
disj : Boolean -> Boolean -> Boolean
disj False False = False
disj _     _     = True

export
proofDisjLeftIdentity : (a : Boolean) -> False `disj` a = a
proofDisjLeftIdentity False = Refl
proofDisjLeftIdentity True  = Refl

export
proofDisjRightIdentity : (a : Boolean) -> a `disj` False = a
proofDisjRightIdentity False = Refl
proofDisjRightIdentity True  = Refl

export
proofDisjLeftAnnihilation : (a : Boolean) -> True `disj` a = True
proofDisjLeftAnnihilation False = Refl
proofDisjLeftAnnihilation True  = Refl

export
proofDisjRightAnnihilation : (a : Boolean) -> a `disj` True = True
proofDisjRightAnnihilation False = Refl
proofDisjRightAnnihilation True  = Refl

export
proofDisjCommutative : (a, b : Boolean) -> a `disj` b = b `disj` a
proofDisjCommutative False b =
  rewrite proofDisjLeftIdentity b in
  rewrite proofDisjRightIdentity b in
  Refl
proofDisjCommutative True b = rewrite proofDisjRightAnnihilation b in Refl

--
-- Conjunction / AND
--

public export
conj : Boolean -> Boolean -> Boolean
conj True True = True
conj _    _    = False

export
proofConjLeftIdentity : (a : Boolean) -> True `conj` a = a
proofConjLeftIdentity False = Refl
proofConjLeftIdentity True  = Refl

export
proofConjRightIdentity : (a : Boolean) -> a `conj` True = a
proofConjRightIdentity False = Refl
proofConjRightIdentity True  = Refl

export
proofConjLeftAnnihilation : (a : Boolean) -> False `conj` a = False
proofConjLeftAnnihilation False = Refl
proofConjLeftAnnihilation True  = Refl

export
proofConjRightAnnihilation : (a : Boolean) -> a `conj` False = False
proofConjRightAnnihilation False = Refl
proofConjRightAnnihilation True  = Refl

export
proofConjCommutative : (a, b : Boolean) -> a `conj` b = b `conj` a
proofConjCommutative False b = rewrite proofConjRightAnnihilation b in Refl
proofConjCommutative True b =
  rewrite proofConjLeftIdentity b in
  rewrite proofConjRightIdentity b in
  Refl

--
-- Util
--

public export
decToBoolean : Dec t -> Boolean
decToBoolean (Yes _) = True
decToBoolean (No  _) = False
