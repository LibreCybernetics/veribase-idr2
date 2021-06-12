module Data.Natural

import Builtin

import Algebra.Relation.Equivalence
import Algebra.Relation.Preorder
import Algebra.Relation.Order

import Algebra.Group.Magma
import Algebra.Group.Semigroup
import Algebra.Group.Monoid

import public Control.Show

import public Data.PrimInteger

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
-- Equivalence
--

data NaturalEquiv : (x, y : Natural) -> Type where
  BothZero : NaturalEquiv Zero Zero
  SuccesorEquiv : NaturalEquiv x y -> NaturalEquiv (Succesor x) (Succesor y)

public export
Uninhabited (NaturalEquiv Zero (Succesor y)) where
  uninhabited BothZero impossible
  uninhabited (SuccesorEquiv _) impossible

public export
Uninhabited (NaturalEquiv (Succesor y) Zero) where
  uninhabited BothZero impossible
  uninhabited (SuccesorEquiv _) impossible

export
proofNotEquivThenNotSuccesorEquiv : {x, y : Natural}
                                  -> Not (NaturalEquiv x y)
                                  -> Not (NaturalEquiv (Succesor x) (Succesor y))
proofNotEquivThenNotSuccesorEquiv h (SuccesorEquiv ctra) = h ctra

public export
Equivalence Natural where
  Equiv = NaturalEquiv

  decEquiv Zero Zero = Yes BothZero
  decEquiv Zero (Succesor _) = No absurd
  decEquiv (Succesor _) Zero = No absurd
  decEquiv (Succesor x) (Succesor y) =
    case decEquiv x y of
      Yes p => Yes $ SuccesorEquiv p
      No cp => No  $ proofNotEquivThenNotSuccesorEquiv cp

--
-- Order
--

data NaturalLTE : (x, y : Natural) -> Type where
  ZeroLTEAny  : NaturalLTE Zero y
  SuccesorLTE : NaturalLTE x    y -> NaturalLTE (Succesor x) (Succesor y)

public export
Uninhabited (NaturalLTE (Succesor y) Zero) where
  uninhabited ZeroLTEAny impossible
  uninhabited (SuccesorLTE _) impossible

export
proofLTEThenLTESuccesor : NaturalLTE x y -> NaturalLTE x (Succesor y)
proofLTEThenLTESuccesor ZeroLTEAny      = ZeroLTEAny
proofLTEThenLTESuccesor (SuccesorLTE p) = SuccesorLTE $ proofLTEThenLTESuccesor p

export
proofNotLTEThenNotSuccesorLTE : Not (NaturalLTE x y) -> Not (NaturalLTE (Succesor x) (Succesor y))
proofNotLTEThenNotSuccesorLTE h (SuccesorLTE ctra) = h ctra

public export
Preorder Natural where
  LTE = NaturalLTE

  decLTE Zero y = Yes ZeroLTEAny
  decLTE (Succesor _) Zero = No absurd
  decLTE (Succesor x) (Succesor y) =
    case decLTE x y of
      Yes p => Yes $ SuccesorLTE p
      No cp => No  $ proofNotLTEThenNotSuccesorLTE cp

  proofReflexivity Zero = ZeroLTEAny
  proofReflexivity (Succesor x) = SuccesorLTE $ proofReflexivity x

  proofTransitivity Zero Zero _ ZeroLTEAny ZeroLTEAny = ZeroLTEAny
  proofTransitivity Zero (Succesor _) (Succesor _) ZeroLTEAny (SuccesorLTE _) = ZeroLTEAny
  proofTransitivity (Succesor x) (Succesor y) (Succesor z) (SuccesorLTE p1) (SuccesorLTE p2) =
    SuccesorLTE $ proofTransitivity x y z p1 p2

public export
Order Natural where
  LT x = NaturalLTE (Succesor x)

  decLT Zero Zero = No absurd
  decLT Zero (Succesor _) = Yes $ SuccesorLTE ZeroLTEAny
  decLT (Succesor _) Zero = No absurd
  decLT (Succesor x) (Succesor y) =
     case decLT x y of
       Yes p => Yes $ SuccesorLTE p
       No cp => No  $ proofNotLTEThenNotSuccesorLTE cp

  proofAntisymetry Zero Zero ZeroLTEAny ZeroLTEAny = BothZero
  proofAntisymetry (Succesor x) (Succesor y) (SuccesorLTE p1) (SuccesorLTE p2) =
    SuccesorEquiv $ proofAntisymetry x y p1 p2

  proofLTThenLTE (SuccesorLTE p) = proofLTEThenLTESuccesor p

  proofLTEThenLTOrEquiv Zero Zero ZeroLTEAny = Right BothZero
  proofLTEThenLTOrEquiv Zero (Succesor _) ZeroLTEAny = Left $ SuccesorLTE ZeroLTEAny
  proofLTEThenLTOrEquiv (Succesor x) (Succesor y) (SuccesorLTE p) =
    case proofLTEThenLTOrEquiv x y p of
      Left  l => Left  $ SuccesorLTE   l
      Right e => Right $ SuccesorEquiv e

--
-- FromInteger
--

natFromPrimInteger : (x : Integer) -> {auto ok : x `GTE` 0} -> Natural
natFromPrimInteger 0 = Zero
natFromPrimInteger x = case (decGTE (prim__sub_Integer x 1) 0) of
  Yes p => Succesor $ assert_total $ natFromPrimInteger $ prim__sub_Integer x 1
  No cp => void $ believe_me () -- TODO: impossible

%builtin IntegerToNatural natFromPrimInteger

natToPrimInteger : Natural -> Integer
natToPrimInteger Zero = 0
natToPrimInteger (Succesor x) = prim__add_Integer 1 $ natToPrimInteger x

%builtin NaturalToInteger natToPrimInteger

public export
SupportPrimIntegerLiteral Natural where
  PrimIntegerRestriction x = x `GTE` 0
  fromPrimInteger = natFromPrimInteger
  toPrimInteger   = natToPrimInteger

public export
Show Natural where
  show = show . toPrimInteger

--
-- Operations
--

public export
plus : (x, y : Natural) -> Natural
plus x Zero = x
plus x (Succesor y) = Succesor $ plus x y

export
proofPlusLeftIdentity : (x : Natural) -> plus Zero x = x
proofPlusLeftIdentity Zero = Refl
proofPlusLeftIdentity (Succesor x) = rewrite proofPlusLeftIdentity x in Refl

export
proofPlusLeftReduction : (x, y : Natural)
                       -> plus (Succesor x) y = Succesor (plus x y)
proofPlusLeftReduction x Zero = Refl
proofPlusLeftReduction x (Succesor y) =
  rewrite proofPlusLeftReduction x y in Refl

export
proofPlusCommutative : (x, y : Natural) -> plus x y = plus y x
proofPlusCommutative x Zero = rewrite proofPlusLeftIdentity x in Refl
proofPlusCommutative x (Succesor y) =
  rewrite proofPlusCommutative x y in
  rewrite proofPlusLeftReduction y x in
  Refl

export
proofPlusAssociative : (x, y, z : Natural)
                     -> plus x (plus y z) = plus (plus x y) z
proofPlusAssociative _ _ Zero = Refl
proofPlusAssociative x y (Succesor z) =
  rewrite proofPlusAssociative x y z in Refl

public export
[NaturalSumMagma] Magma Natural where
  (<>) = plus

public export
[NaturalSumSemigroup] Semigroup Natural using NaturalSumMagma where
  proofAssociativity = proofPlusAssociative

public export
[NaturalSumMonoid] Monoid Natural using NaturalSumSemigroup where
  id = Zero

  proofLeftIdentity = proofPlusLeftIdentity
  proofRightIdentity _ = Refl

public export
minus : (x, y : Natural) -> {auto ok : x `GTE` y} -> Natural
minus x Zero = x
minus (Succesor x) (Succesor y) {ok=(SuccesorLTE p)} = minus x y

public export
mult : (x, y : Natural) -> Natural
mult _ Zero = Zero
mult x (Succesor y) = x `plus` mult x y

export
proofMultLeftIdentity : (x : Natural) -> mult (Succesor Zero) x = x
proofMultLeftIdentity Zero = Refl
proofMultLeftIdentity (Succesor x) =
  rewrite proofMultLeftIdentity x in
  rewrite proofPlusLeftReduction Zero x in
  rewrite proofPlusLeftIdentity x in
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
  rewrite proofPlusLeftReduction x (mult (Succesor x) y) in
  rewrite proofPlusLeftReduction y (mult (Succesor y) x) in
  rewrite proofMultCommutative (Succesor x) y in
  rewrite proofMultCommutative (Succesor y) x in
  rewrite proofMultCommutative x y in
  rewrite proofPlusAssociative x y (mult y x) in
  rewrite proofPlusAssociative y x (mult y x) in
  rewrite proofPlusCommutative x y in
  Refl

export
proofMultLeftReduction : (x, y : Natural)
                       -> mult (Succesor x) y = plus y (mult x y)
proofMultLeftReduction x y =
  rewrite proofMultCommutative (Succesor x) y in
  rewrite proofMultCommutative x y in
  Refl

export
proofMultLeftDistributesPlus : (x, y, z : Natural)
                             -> mult x (plus y z) = plus (mult x y) (mult x z)
proofMultLeftDistributesPlus Zero y z =
  rewrite proofMultLeftAnnihilation y in
  rewrite proofMultLeftAnnihilation z in
  rewrite proofMultLeftAnnihilation (plus y z) in
  Refl
proofMultLeftDistributesPlus (Succesor x) y z =
  rewrite proofMultLeftReduction x y in
  rewrite proofMultLeftReduction x z in
  rewrite proofMultLeftReduction x (plus y z) in
  rewrite proofMultLeftDistributesPlus x y z in
  rewrite proofPlusAssociative (plus y (mult x y)) z (mult x z) in
  rewrite proofPlusCommutative (plus y (mult x y)) z in
  rewrite proofPlusAssociative z y (mult x y) in
  rewrite proofPlusCommutative z y in
  rewrite proofPlusAssociative (plus y z) (mult x y) (mult x z) in
  Refl


public export
[NaturalMultMagma] Magma Natural where
  (<>) = mult

public export
[NaturalMultSemigroup] Semigroup Natural using NaturalMultMagma where
  proofAssociativity x y Zero = Refl
  proofAssociativity x y (Succesor z) =
    rewrite proofMultLeftDistributesPlus x y (mult y z) in
    rewrite proofAssociativity x y z in
    Refl

public export
[NaturalMultMonoid] Monoid Natural using NaturalMultSemigroup where
  id = Succesor Zero

  proofLeftIdentity = proofMultLeftIdentity
  proofRightIdentity _ = Refl

public export
divRem : (x, y : Natural) -> {auto ok : NotZero y} -> (Natural, Natural)
divRem x y = case decLTE y x of
  Yes _ => let (d, r) := divRem (x `minus` y) y in (Succesor d, r)
  No  _ => (Zero, x)

public export
div : (x, y : Natural) -> {auto ok : NotZero y} -> Natural
div x y = fst $ divRem x y

public export
rem : (x, y : Natural) -> {auto ok : NotZero y} -> Natural
rem x y = snd $ divRem x y
