module Data.Natural

import Builtin

import Algebra.Relation.Equivalence
import Algebra.Relation.Preorder

%default total

public export
data Natural = Zero | Succesor Natural

%builtin Natural Natural

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

public export
proofNotEquivThenNotSuccesorEquiv : {x, y : Natural}
                                  -> Not (NaturalEquiv x y)
                                  -> Not (NaturalEquiv (Succesor x) (Succesor y))
proofNotEquivThenNotSuccesorEquiv h (SuccesorEquiv ctra) = h ctra

Equivalence Natural where
  Equiv = NaturalEquiv

  decEquiv Zero Zero = Yes BothZero
  decEquiv Zero (Succesor _) = No absurd
  decEquiv (Succesor _) Zero = No absurd
  decEquiv (Succesor x) (Succesor y) =
    case decEquiv x y of
      Yes p => Yes $ SuccesorEquiv p
      No cp => No $ proofNotEquivThenNotSuccesorEquiv cp

--
-- Order
--

data NaturalLTE : (x, y : Natural) -> Type where
  ZeroLTEAny : NaturalLTE Zero y
  SuccesorLTE : NaturalLTE x y -> NaturalLTE (Succesor x) (Succesor y)

public export
Uninhabited (NaturalLTE (Succesor y) Zero) where
  uninhabited ZeroLTEAny impossible
  uninhabited (SuccesorLTE _) impossible

public export
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
      No cp => No $ proofNotLTEThenNotSuccesorLTE cp

  proofReflexivity Zero = ZeroLTEAny
  proofReflexivity (Succesor x) = SuccesorLTE $ proofReflexivity x

  proofTransitivity Zero        Zero            z  ZeroLTEAny  ZeroLTEAny     = ZeroLTEAny
  proofTransitivity Zero (Succesor y) (Succesor z) ZeroLTEAny (SuccesorLTE p) = ZeroLTEAny
  proofTransitivity (Succesor x) (Succesor y) (Succesor z) (SuccesorLTE p1) (SuccesorLTE p2) =
    SuccesorLTE $ proofTransitivity x y z p1 p2
