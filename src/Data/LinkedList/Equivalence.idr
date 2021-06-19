module Data.LinkedList.Equivalence

import Builtin

import Algebra.Relation.Equivalence

import public Data.LinkedList.Basic

%default total

public export
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

decLinkedListEquiv : (e : Equivalence t) => (a, b : LinkedList t)
                   -> Dec (LinkedListEquiv @{e} a b)
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
