module Data.Optional

import Builtin

import Algebra.Equivalence
import Algebra.Functor

%default total

public export
data Optional t = Nothing | Some t

data OptionalEquiv : (a, b : Optional t) -> Type where
  BothNothing : OptionalEquiv Nothing Nothing
  BothSame : Equivalence t => {a, b : t} -> (ok : Equiv a b) -> OptionalEquiv (Some a) (Some b)

public export
Uninhabited (OptionalEquiv Nothing (Some b)) where
  uninhabited BothNothing  impossible
  uninhabited (BothSame _) impossible

public export
Uninhabited (OptionalEquiv (Some a) Nothing) where
  uninhabited BothNothing  impossible
  uninhabited (BothSame _) impossible

public export
fromNotEquiv : Equivalence t => {a, b : t} -> (ok : Not (Equiv a b)) -> Not (OptionalEquiv (Some a) (Some b))
fromNotEquiv ok BothNothing impossible
fromNotEquiv ok (BothSame ctr) = ?ctra

public export
Equivalence t => Equivalence (Optional t) where
  Equiv = OptionalEquiv

  decEquiv Nothing  Nothing  = Yes $ BothNothing
  decEquiv Nothing  (Some _) = No $ absurd
  decEquiv (Some _) Nothing  = No $ absurd
  decEquiv (Some a) (Some b) with (decEquiv a b)
    decEquiv (Some a) (Some b) | (Yes prf) = Yes $ BothSame prf
    decEquiv (Some a) (Some b) | (No ctra) = No $ fromNotEquiv ctra

public export
Functor Optional where
  map f Nothing  = Nothing
  map f (Some a) = Some . f $ a

  proofIdentity Nothing  = Refl
  proofIdentity (Some a) = Refl

  proofComposition f g Nothing  = Refl
  proofComposition f g (Some a) = Refl
