module Data.LinkedList.Applicative

import Builtin

import Algebra.Control.Functor
import Algebra.Control.Applicative

import public Data.LinkedList.Basic
import public Data.LinkedList.Functor

%default total

public export
app : LinkedList (a -> b) -> LinkedList a -> LinkedList b
app Nil     _ = Nil
app (f::fs) l = (f <$> l) `concat` app fs l

public export
appNil : (f : LinkedList (a -> b)) -> f `app` Nil = Nil
appNil Nil     = Refl
appNil (f::fs) = rewrite appNil fs in Refl

public export
Applicative LinkedList where
  pure x = [x]

  (<*>) = app

  proofIdentity Nil = Refl
  proofIdentity (_::xs) with (Functor.proofIdentity xs)
    proofIdentity (_::xs) | prf =
      rewrite proofConcatRightIdentity (identity <$> xs) in
      rewrite prf in Refl

  proofHomomorphism f x = Refl

  proofInterchange Nil x = Refl
  proofInterchange (f::fs) x = rewrite proofInterchange fs x in Refl

  proofComposition Nil Nil _ = Refl
  proofComposition Nil (_::gs) _ =
    rewrite appNil gs in
    -- rewrite proofConcatRightIdentity ((.) <$> gs) in
    ?holeComposition1
  proofComposition (f::fs) gs _ =
    -- rewrite proofConcatRightIdentity ((.) <$> gs) in
    ?holeComposition2
