This a an alternative prelude and base package taking inspiration from:
 - Agda-stdlib
 - Haskell (base, rio, protolude, relude, foundation, rebase)
 - Idris (Idris1 Base/Contrib/Efffects/Network and Idris2)
 - Scala (Typelevel's cats, ScalaZ)

Veribase-Core

 - Builtin (From Idris2)
 - Bool
 - Either

Depending on Builtin

 - Algebra.Group
 - Algebra.Ring

Depending on Builtin and Bool

 - Relation (Since they have Bool Return Type)

Depending on Builtin, Bool, and Order:

 - Algebra.Lattice

Veribase-Containers (TODO)
