module Data.LinkedList.Functor

import Builtin

import Algebra.Control.Functor

import public Data.LinkedList.Basic

public export
Functor LinkedList where
  _ <$> Nil = Nil
  f <$> (h::t) = f h :: f <$> t

  proofIdentity Nil = Refl
  proofIdentity (_::t) with (proofIdentity t)
    proofIdentity (_::_) | prf = rewrite prf in Refl

  proofComposition f g Nil    = Refl
  proofComposition f g (_::t) = rewrite proofComposition f g t in Refl
