module Data.Natural.Basic

import Builtin

%default total

public export
data Natural = Zero | Succesor Natural

%builtin Natural Natural

--
-- Restrictions
--

public export
data NotZero : Natural -> Type where
  IsNotZero : NotZero (Succesor _)

public export
Uninhabited (NotZero Zero) where
  uninhabited IsNotZero impossible

--
-- Operations
--

-- Addition

public export
add : (x, y : Natural) -> Natural
add x Zero = x
add x (Succesor y) = Succesor $ add x y

export
proofAddLeftIdentity : (x : Natural) -> add Zero x = x
proofAddLeftIdentity Zero = Refl
proofAddLeftIdentity (Succesor x) = rewrite proofAddLeftIdentity x in Refl

export
proofAddLeftReduction : (x, y : Natural)
                       -> add (Succesor x) y = Succesor (add x y)
proofAddLeftReduction x Zero = Refl
proofAddLeftReduction x (Succesor y) =
  rewrite proofAddLeftReduction x y in Refl

export
proofAddCommutative : (x, y : Natural) -> add x y = add y x
proofAddCommutative x Zero = rewrite proofAddLeftIdentity x in Refl
proofAddCommutative x (Succesor y) =
  rewrite proofAddCommutative x y in
  rewrite proofAddLeftReduction y x in
  Refl

export
proofAddAssociative : (x, y, z : Natural)
                     -> add x (add y z) = add (add x y) z
proofAddAssociative _ _ Zero = Refl
proofAddAssociative x y (Succesor z) =
  rewrite proofAddAssociative x y z in Refl

-- Diff

public export
diff : (x, y : Natural) -> Natural
diff Zero y = y
diff x Zero = x
diff (Succesor x) (Succesor y) = diff x y

-- Mult

public export
mult : (x, y : Natural) -> Natural
mult _ Zero = Zero
mult x (Succesor y) = x `add` mult x y

export
proofMultLeftIdentity : (x : Natural) -> mult (Succesor Zero) x = x
proofMultLeftIdentity Zero = Refl
proofMultLeftIdentity (Succesor x) =
  rewrite proofMultLeftIdentity x in
  rewrite proofAddLeftReduction Zero x in
  rewrite proofAddLeftIdentity x in
  Refl

export
proofMultLeftAnnihilation : (x : Natural) -> mult Zero x = Zero
proofMultLeftAnnihilation Zero = Refl
proofMultLeftAnnihilation (Succesor x) =
  rewrite proofMultLeftAnnihilation x in Refl

export
proofMultRightAnnihilation : (x : Natural) -> mult x Zero = Zero
proofMultRightAnnihilation Zero = Refl
proofMultRightAnnihilation (Succesor x) =
  rewrite proofMultRightAnnihilation x in Refl

export
proofMultCommutative : (x, y : Natural) -> mult x y = mult y x
proofMultCommutative Zero Zero = Refl
proofMultCommutative Zero (Succesor y) =
  rewrite proofMultCommutative Zero y in Refl
proofMultCommutative (Succesor x) Zero =
  rewrite proofMultCommutative Zero x in Refl
proofMultCommutative (Succesor x) (Succesor y) =
  rewrite proofAddLeftReduction x (mult (Succesor x) y) in
  rewrite proofAddLeftReduction y (mult (Succesor y) x) in
  rewrite proofMultCommutative (Succesor x) y in
  rewrite proofMultCommutative (Succesor y) x in
  rewrite proofMultCommutative x y in
  rewrite proofAddAssociative x y (mult y x) in
  rewrite proofAddAssociative y x (mult y x) in
  rewrite proofAddCommutative x y in
  Refl

export
proofMultLeftReduction : (x, y : Natural)
                       -> mult (Succesor x) y = add y (mult x y)
proofMultLeftReduction x y =
  rewrite proofMultCommutative (Succesor x) y in
  rewrite proofMultCommutative x y in
  Refl

export
proofMultLeftDistributesAdd : (x, y, z : Natural)
                             -> mult x (add y z) = add (mult x y) (mult x z)
proofMultLeftDistributesAdd Zero y z =
  rewrite proofMultLeftAnnihilation y in
  rewrite proofMultLeftAnnihilation z in
  rewrite proofMultLeftAnnihilation (add y z) in
  Refl
proofMultLeftDistributesAdd (Succesor x) y z =
  rewrite proofMultLeftReduction x y in
  rewrite proofMultLeftReduction x z in
  rewrite proofMultLeftReduction x (add y z) in
  rewrite proofMultLeftDistributesAdd x y z in
  rewrite proofAddAssociative (add y (mult x y)) z (mult x z) in
  rewrite proofAddCommutative (add y (mult x y)) z in
  rewrite proofAddAssociative z y (mult x y) in
  rewrite proofAddCommutative z y in
  rewrite proofAddAssociative (add y z) (mult x y) (mult x z) in
  Refl

export
proofMultRightDistributesAdd : (x, y, z : Natural)
                              -> mult (add x y) z = add (mult x z) (mult y z)
proofMultRightDistributesAdd x y z =
  rewrite proofMultCommutative (add x y) z in
  rewrite proofMultLeftDistributesAdd z x y in
  rewrite proofMultCommutative z x in
  rewrite proofMultCommutative z y in
  Refl
