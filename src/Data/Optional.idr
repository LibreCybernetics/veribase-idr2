module Data.Optional

import Builtin

import Algebra.Control.Applicative
import Algebra.Relation.Equivalence
import Algebra.Control.Functor
import Algebra.Control.Monad

%default total

public export
data Optional t = Nothing | Some t

data OptionalEquiv : Equivalence t => (a, b : Optional t) -> Type where
  BothNothing : (e : Equivalence t) => OptionalEquiv @{e} Nothing Nothing
  BothSame : (e : Equivalence t) => {a, b : t} -> (ok : Equiv a b)
           -> OptionalEquiv @{e} (Some a) (Some b)

public export
(e : Equivalence t) => Uninhabited (OptionalEquiv @{e} Nothing (Some b)) where
  uninhabited BothNothing  impossible
  uninhabited (BothSame _) impossible

public export
(e : Equivalence t) => Uninhabited (OptionalEquiv @{e} (Some a) Nothing) where
  uninhabited BothNothing  impossible
  uninhabited (BothSame _) impossible

public export
fromNotEquiv : Equivalence t => {a, b : t} -> (ok : Not (Equiv a b)) -> Not (OptionalEquiv (Some a) (Some b))
fromNotEquiv ok BothNothing impossible
fromNotEquiv ok (BothSame ctr) = ok ctr

public export
Equivalence t => Equivalence (Optional t) where
  Equiv = OptionalEquiv

  decEquiv Nothing  Nothing  = Yes $ BothNothing
  decEquiv Nothing  (Some _) = No $ absurd
  decEquiv (Some _) Nothing  = No $ absurd
  decEquiv (Some a) (Some b) = case (decEquiv a b) of
    (Yes prf) => Yes $ BothSame prf
    (No ctra) => No $ fromNotEquiv ctra

public export
Functor Optional where
  map f Nothing  = Nothing
  map f (Some a) = Some . f $ a

  proofIdentity Nothing  = Refl
  proofIdentity (Some a) = Refl

  proofComposition f g Nothing  = Refl
  proofComposition f g (Some a) = Refl

public export
Applicative Optional where
  pure = Some

  Nothing <*> _ = Nothing
  _ <*> Nothing = Nothing
  (Some f) <*> (Some x) = Some $ f x

  proofIdentity Nothing  = Refl
  proofIdentity (Some x) = Refl

  proofComposition Nothing  Nothing  _ = Refl
  proofComposition Nothing  (Some g) _ = Refl
  proofComposition (Some f) Nothing  _ = Refl
  proofComposition (Some f) (Some g) Nothing  = Refl
  proofComposition (Some f) (Some g) (Some x) = Refl

  proofHomomorphism f x = Refl

  proofInterchange Nothing  x = Refl
  proofInterchange (Some f) x = Refl

public export
Monad Optional where
  Nothing >>= _ = Nothing
  (Some x) >>= f = f x

  proofLeftIdentity x f = Refl

  proofRightIdentity Nothing  = Refl
  proofRightIdentity (Some x) = Refl

  proofAssociativity Nothing  f g = Refl
  proofAssociativity (Some x) f g = Refl
