import WolfeSimplex.Defs.Induced

/-!
# Scaling an LP (paper: Section 3 (`sec:equivalence`) (integrality discussion))

Trusted definition for the paragraph "Integrality" of Section 3 (`sec:equivalence`) (integrality
discussion), which
justifies assumption (A1): multiplying a row of `A` and the corresponding entry of `b` by a
positive number, and `c` by a positive number `ω`, does not change the simplex runs.
(The paper multiplies by positive integers; here any positive real factors are allowed.)
-/

namespace WolfeSimplex

namespace LP

variable {m n : ℕ} (P : LP m n)

/-- The LP with row `i` of `A` and the entry `b_i` multiplied by `r i`, and the cost vector
`c` multiplied by `ω` (paper: Section 3 (`sec:equivalence`) (integrality discussion)). -/
def scale (r : Fin m → ℝ) (ω : ℝ) : LP m n where
  A := Matrix.of fun i j ↦ r i * P.A i j
  b := fun i ↦ r i * P.b i
  c := fun j ↦ ω * P.c j

end LP

end WolfeSimplex
