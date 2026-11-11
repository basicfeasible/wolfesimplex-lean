import WolfeSimplex

/-! Run with `lake env lean scripts/CheckConstruction.lean`.
Executable smoke check with an admissible LP, including a negative coordinate.
The universal correctness and resource claims are kernel-checked theorems in
Construction/Budget.lean; these evaluations are not used as mathematical proofs. -/

open WolfeSimplex

#guard ((Construction.atoms Sanity.tiny).toList.map Vector.toList) ==
  [[1572864, 1649267441664], [1572864, -824633720832]]
#guard (Construction.run Sanity.tiny).operations == 42
#guard Construction.inputSize Sanity.tiny == 16
