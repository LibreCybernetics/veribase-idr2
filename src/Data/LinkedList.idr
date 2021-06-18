module Data.LinkedList

import Builtin

import Algebra.Relation.Equivalence

import Algebra.Control.Functor
import Algebra.Control.Applicative
import Algebra.Control.Monad

import Algebra.Group.Magma
import Algebra.Group.Semigroup
import Algebra.Group.Monoid

%default total

infixr 7 ::

public export
data LinkedList t = Nil | (::) t (LinkedList t)

data LinkedListEquiv : Equivalence t => (a, b : LinkedList t) -> Type where
  BothEmpty : (e : Equivalence t) => LinkedListEquiv @{e} Nil Nil
  EquivHeadAndTail : (e : Equivalence t) => {a, b : t} -> {x, y : LinkedList t}
                   -> (ok1: Equiv a b) -> (ok2: LinkedListEquiv x y)
                   -> LinkedListEquiv @{e} (a :: x) (b :: y)

public export
(e : Equivalence a) => Uninhabited (LinkedListEquiv @{e} Nil (h :: t)) where
  uninhabited BothEmpty impossible
  uninhabited (EquivHeadAndTail h t) impossible

public export
(e : Equivalence a) => Uninhabited (LinkedListEquiv @{e} (h :: t) Nil) where
  uninhabited BothEmpty impossible
  uninhabited (EquivHeadAndTail h t) impossible

public export
fromNotEquivHead : (e : Equivalence t) => {a, b : t} -> (ok: Not (Equiv a b))
                 -> Not (LinkedListEquiv @{e} (a :: x) (b :: y))
fromNotEquivHead ctr (EquivHeadAndTail prf _) = ctr prf

public export
fromNotEquivTail : (e : Equivalence t) => (ok: Not (LinkedListEquiv @{e} x y))
                 -> Not (LinkedListEquiv @{e} (a :: x) (b :: y))
fromNotEquivTail ctr (EquivHeadAndTail _ prf) = ctr prf

decLinkedListEquiv : (e : Equivalence t) => (a, b : LinkedList t) -> Dec (LinkedListEquiv @{e} a b)
decLinkedListEquiv Nil Nil = Yes BothEmpty
decLinkedListEquiv Nil (_::_) = No absurd
decLinkedListEquiv (_::_) Nil = No absurd
decLinkedListEquiv @{e} (h1::t1) (h2::t2) =
  case (decEquiv @{e} h1 h2, decLinkedListEquiv t1 t2) of
    (Yes prf1, Yes prf2) => Yes $ EquivHeadAndTail prf1 prf2
    (Yes prf1, No ctra2) => No $ fromNotEquivTail @{e} ctra2
    (No ctra1, _) => No $ fromNotEquivHead @{e} ctra1

public export
(Equivalence t) => Equivalence (LinkedList t) where
  Equiv    = LinkedListEquiv
  decEquiv = decLinkedListEquiv

public export
concat : LinkedList t -> LinkedList t -> LinkedList t
concat Nil     y = y
concat (x::xs) y = x :: concat xs y

public export
concatNil : (l : LinkedList t) -> concat l Nil = l
concatNil Nil = Refl
concatNil (x::xs) = rewrite concatNil xs in Refl

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

public export
Functor LinkedList where
  _ <$> Nil = Nil
  f <$> (h::t) = f h :: f <$> t

  proofIdentity Nil = Refl
  proofIdentity (_::t) with (proofIdentity t)
    proofIdentity (_::_) | prf = rewrite prf in Refl

  proofComposition f g Nil    = Refl
  proofComposition f g (_::t) = rewrite proofComposition f g t in Refl

public export
app : LinkedList (a -> b) -> LinkedList a -> LinkedList b
app Nil     _ = Nil
app (f::fs) l = (f <$> l) <> app fs l

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
      rewrite concatNil (identity <$> xs) in
      rewrite prf in Refl

  proofHomomorphism f x = Refl

  proofInterchange Nil x = Refl
  proofInterchange (f::fs) x = rewrite proofInterchange fs x in Refl

  proofComposition Nil Nil _ = Refl
  proofComposition Nil (_::gs) _ =
    rewrite appNil gs in
    -- rewrite concatNil ((.) <$> gs) in
    ?holeComposition1
  proofComposition (f::fs) gs _ =
    -- rewrite concatNil ((.) <$> gs) in
    ?holeComposition2

public export
Monad LinkedList where
  Nil >>= _ = Nil
  (x::xs) >>= f = f x <> (xs >>= f)

  proofLeftIdentity x f = rewrite concatNil (f x) in Refl

  proofRightIdentity Nil = Refl
  proofRightIdentity (x::xs) with (Monad.proofRightIdentity xs)
    proofRightIdentity (_::_) | prf = rewrite prf in Refl

  proofAssociative Nil f g = Refl
  proofAssociative (x::xs) f g with (f x)
    proofAssociative (x::xs) f g | Nil = rewrite proofAssociative xs f g in Refl
    proofAssociative (x::xs) f g | (r::rs) = ?holeAssociative
