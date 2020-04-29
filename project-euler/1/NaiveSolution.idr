module NaiveSolution

import Verilude

import Control.Integral
import Data.Nat.Integral

main : LinkedList Nat
main = filter (`divBy` (the Nat 3)) [(the Nat 1)..1000]
