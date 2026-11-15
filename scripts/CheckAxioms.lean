module

import Solution

/-!
# Axiom check

`lake env lean scripts/CheckAxioms.lean` (after `lake build`) prints the axioms that each compared
theorem of `Solution.lean` depends on. Palomar permits only `propext`, `Classical.choice` and
`Quot.sound`.
-/

#print axioms GwH34.no_good_53
#print axioms GwH34.no_good_of_le
#print axioms GwH34.exists_good_52
#print axioms GwH34.H_four
