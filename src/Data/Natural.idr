module Data.Natural

import Builtin

import Algebra.Relation.Equivalence

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

Uninhabited (NaturalEquiv Zero (Succesor y)) where
  uninhabited BothZero impossible
  uninhabited (SuccesorEquiv _) impossible

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
