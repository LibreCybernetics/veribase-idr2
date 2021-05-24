module Data.LinkedList

import Builtin

import Algebra.Equivalence
import Algebra.Functor

%default total

infixr 7 ::

public export
data LinkedList t = Nil | (::) t (LinkedList t)

data LinkedListEquiv : (a, b : LinkedList t) -> Type where
  BothEmpty : LinkedListEquiv Nil Nil
  EquivHeadAndTail : Equivalence t => {a, b : t} -> {x, y : LinkedList t}
                   -> (ok1: Equiv a b) -> (ok2: LinkedListEquiv x y)
                   -> LinkedListEquiv (a :: x) (b :: y)

public export
Uninhabited (LinkedListEquiv Nil (h :: t)) where
  uninhabited BothEmpty impossible
  uninhabited (EquivHeadAndTail h t) impossible

public export
Uninhabited (LinkedListEquiv (h :: t) Nil) where
  uninhabited BothEmpty impossible
  uninhabited (EquivHeadAndTail h t) impossible

public export
fromNotEquivHead : Equivalence t => {a, b : t} -> (ok: Not (Equiv a b)) -> Not (LinkedListEquiv (a :: x) (b :: y))
fromNotEquivHead ctr BothEmpty impossible
fromNotEquivHead ctr (EquivHeadAndTail prf _) = ?ctra

public export
fromNotEquivTail : (ok: Not (LinkedListEquiv x y)) -> Not (LinkedListEquiv (a :: x) (b :: y))
fromNotEquivTail ctr BothEmpty impossible
fromNotEquivTail ctr (EquivHeadAndTail _ prf) = ctr prf

public export
Equivalence t => Equivalence (LinkedList t) where
  Equiv = LinkedListEquiv

  decEquiv Nil Nil = Yes $ BothEmpty
  decEquiv Nil (_ :: _) = No $ absurd
  decEquiv (_ :: _) Nil = No $ absurd
  decEquiv (h1 :: t1) (h2 :: t2) = case (decEquiv h1 h2, decEquiv t1 t2) of
    (Yes prf1, Yes prf2) => Yes $ EquivHeadAndTail prf1 prf2
    (Yes prf1, No ctra2) => No $ fromNotEquivTail ctra2
    (No ctra1, _) => No $ fromNotEquivHead ctra1
    _ => ?impossibleCase -- TODO: Upstream bug

public export
Functor LinkedList where
  map _ Nil = Nil
  map f (h::t) = f h :: map f t

  proofIdentity Nil = Refl
  proofIdentity (h::t) with (proofIdentity t)
    proofIdentity (h::t) | prf = rewrite prf in Refl

  proofComposition f g Nil = Refl
  proofComposition f g (h::t) = rewrite proofComposition f g t in Refl
