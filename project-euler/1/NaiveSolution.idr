module NaiveSolution

import Prelude

import Data.Integral
import Data.Nat.Integral

main : LinkedList Nat
main = filter (`divBy` (the Nat 3)) [(the Nat 1)..100]
