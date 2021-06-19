module Data.Natural.Order

import Builtin

import Algebra.Relation.Equivalence
import Algebra.Relation.Preorder
import Algebra.Relation.Order

import public Data.Natural.Basic
import public Data.Natural.Equivalence

%default total

public export
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
