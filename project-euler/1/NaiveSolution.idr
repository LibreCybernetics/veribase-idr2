module NaiveSolution

import Verilude

main : LinkedList Nat
main = filter (≡ (fromInteger 10)) [(fromInteger 1)..(fromInteger 10)]
