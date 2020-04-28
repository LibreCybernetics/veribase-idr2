module Data.LinkedList

%default total

infix 5 ::

public export
data LinkedList a = Nil | (::) a (LinkedList a)
