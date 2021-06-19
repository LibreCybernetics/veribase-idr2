module Data.LinkedList.Basic

import Builtin

%default total

infixr 7 ::

public export
data LinkedList t = Nil | (::) t (LinkedList t)

public export
concat : LinkedList t -> LinkedList t -> LinkedList t
concat Nil     y = y
concat (x::xs) y = x :: concat xs y

export
proofConcatRightIdentity : (l : LinkedList t) -> concat l Nil = l
proofConcatRightIdentity Nil = Refl
proofConcatRightIdentity (x::xs) = rewrite proofConcatRightIdentity xs in Refl
