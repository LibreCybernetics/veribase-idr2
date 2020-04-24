# Intro

This a an alternative prelude and base package taking inspiration from:
 - Agda-stdlib
 - Haskell (base, rio, protolude, relude, foundation, rebase)
 - Idris (Idris1 Base/Contrib/Efffects/Network and Idris2)
 - Scala (Typelevel's cats, ScalaZ)

Design goals are math-based, interface-focused with proofs, and totality

# Structure

## veribase-core (Base types and most interfaces)

 - Builtin (From Idris2)
 - Bool
 - Either

Depending on Builtin

 - Algebra.Group
 - Algebra.Ring

Depending on Builtin, Bool, Either

 - Relation (Since they have Bool Return Type)

Depending on Builtin, Bool, Either, and Order:

 - Algebra.Lattice
 - Algebra.BooleanAlgebra

## veribase-containers (TODO: Next)
