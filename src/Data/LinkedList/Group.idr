module Data.LinkedList.Group

import Builtin

import Algebra.Group.Magma
import Algebra.Group.Semigroup
import Algebra.Group.Monoid

import public Data.LinkedList.Basic

%default total

public export
Magma (LinkedList t) where
  (<>) = concat

public export
Semigroup (LinkedList t) where
  proofAssociative Nil     _ _ = Refl
  proofAssociative (x::xs) y z = rewrite proofAssociative xs y z in Refl

public export
Monoid (LinkedList t) where
  id = Nil

  proofLeftIdentity Nil     = Refl
  proofLeftIdentity (x::xs) = rewrite Monoid.proofLeftIdentity xs in Refl

  proofRightIdentity Nil     = Refl
  proofRightIdentity (y::ys) = rewrite Monoid.proofRightIdentity ys in Refl
