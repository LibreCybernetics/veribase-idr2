module Data.Boolean.Group

import Builtin

import Algebra.Group.Magma
import Algebra.Group.Semigroup
import Algebra.Group.Monoid

import public Data.Boolean.Basic

%default total

public export
[BooleanDisjMagma] Magma Boolean where
  (<>) = disj

public export
[BooleanDisjCommutativeMagma] CommutativeMagma Boolean using BooleanDisjMagma where
  proofCommutative = proofDisjCommutative


public export
[BooleanDisjSemigroup] Semigroup Boolean using BooleanDisjMagma where
  proofAssociative False b c =
    rewrite proofDisjLeftIdentity b in
    rewrite proofDisjLeftIdentity (b `disj` c) in
    Refl
  proofAssociative True b c = Refl

public export
[BooleanDisjCommutativeSemigroup] CommutativeSemigroup Boolean using BooleanDisjCommutativeMagma BooleanDisjSemigroup where

public export
[BooleanDisjMonoid] Monoid Boolean using BooleanDisjSemigroup where
  id = False

  proofLeftIdentity  = proofDisjLeftIdentity
  proofRightIdentity = proofDisjRightIdentity

public export
[BooleanDisjCommutativeMonoid] CommutativeMonoid Boolean using BooleanDisjCommutativeSemigroup BooleanDisjMonoid where

public export
[BooleanConjMagma] Magma Boolean where
  (<>) = conj

public export
[BooleanConjCommutativeMagma] CommutativeMagma Boolean using BooleanConjMagma where
  proofCommutative = proofConjCommutative

public export
[BooleanConjSemigroup] Semigroup Boolean using BooleanConjMagma where
  proofAssociative False b c = Refl
  proofAssociative True  b c =
    rewrite proofConjLeftIdentity b in
    rewrite proofConjLeftIdentity (b `conj` c) in
    Refl

public export
[BooleanConjMonoid] Monoid Boolean using BooleanConjSemigroup where
  id = True

  proofLeftIdentity  = proofConjLeftIdentity
  proofRightIdentity = proofConjRightIdentity
