module Data.Either

import public Builtin

import Algebra.Control.Functor
import Algebra.Control.Applicative
import Algebra.Control.Monad

public export
data Either a b = Left a | Right b

public export
Functor (Either t) where
  map f (Left x)  = Left x
  map f (Right x) = Right $ f x

  proofIdentity (Left _)  = Refl
  proofIdentity (Right _) = Refl

  proofComposition f g (Left _) = Refl
  proofComposition f g (Right _) = Refl

public export
Applicative (Either t) where
  pure = Right

  (Left x)  <*> _         = Left x
  (Right _) <*> (Left y)  = Left y
  (Right f) <*> (Right x) = Right $ f x

  proofIdentity (Left  _) = Refl
  proofIdentity (Right _) = Refl

  proofHomomorphism f x = Refl

  proofInterchange (Left _)  _ = Refl
  proofInterchange (Right _) _ = Refl

  proofComposition (Left _)  (Left _)  _ = Refl
  proofComposition (Left _)  (Right _) _ = Refl
  proofComposition (Right _) (Left _)  _ = Refl
  proofComposition (Right _) (Right _) x = case x of
    Left x => Refl
    Right x => Refl

public export
Monad (Either t) where
  (Left x)  `bind` _ = Left x
  (Right x) `bind` f = f x

  proofLeftIdentity _ _ = Refl

  proofRightIdentity (Left  _) = Refl
  proofRightIdentity (Right _) = Refl

  proofAssociativity (Left  _) f g = Refl
  proofAssociativity (Right _) f g = Refl
