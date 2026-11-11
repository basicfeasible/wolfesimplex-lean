import Mathlib

/-!
# The simplex method (paper: Section 2.1 (`sec:simplex`))

Trusted definitions for linear programs in standard form and the simplex method,
following Section 2.1 (`sec:simplex`) and Definition 1 (`def:basis`) of the paper.

## Conventions (differences in form from the paper)

* All numbers are real numbers `ℝ`. The paper uses `ℚ` for the LP data; every
  rational LP is in particular a real LP, and all definitions below read the same.
* Labels are `Fin n = {0, …, n-1}` instead of `[n] = {1, …, n}`.
* A vector `x ∈ ℝⁿ` is a function `x : Fin n → ℝ`. A vector in `ℝ^B` for a label
  set `B` is always identified with its extension by zeros (as in the paper).
* Several objects are defined in the paper by a formula with an inverse matrix,
  e.g. `x^B_B = A_B⁻¹ b`. Here they are defined as *the unique vector with the
  defining property* (e.g. `A x = b` and `x_j = 0` for `j ∉ B`). For a basis `B`,
  these properties have exactly one solution, and it is the paper's vector.
  Technically, `Classical.epsilon p` denotes "some element satisfying `p`, if one
  exists" (an arbitrary value otherwise; that case is never used for bases).
* The paper's standing assumption "`A` has rank `m ≥ 1`" is not built into the
  structure `LP`; it is a hypothesis where needed (see `IntLP.IsAdmissible`).
-/

namespace WolfeSimplex

open Finset Matrix

/-- A linear program `min cᵀx subject to Ax = b, x ≥ 0` (paper: (LP), `eq:lp`)
with `m` equality constraints and `n` variables (labels `Fin n`). -/
structure LP (m n : ℕ) where
  /-- the constraint matrix `A ∈ ℝ^{m×n}` -/
  A : Matrix (Fin m) (Fin n) ℝ
  /-- the right-hand side `b ∈ ℝ^m` -/
  b : Fin m → ℝ
  /-- the cost vector `c ∈ ℝⁿ` -/
  c : Fin n → ℝ

namespace LP

variable {m n : ℕ} (P : LP m n)

/-- Column `A_j` of the constraint matrix. -/
def col (j : Fin n) : Fin m → ℝ := fun i ↦ P.A i j

/-- `x` is a feasible point: `Ax = b` and `x ≥ 0`, i.e. `x` lies in the feasible
set `𝒫` of the paper. -/
def IsFeasible (x : Fin n → ℝ) : Prop :=
  P.A *ᵥ x = P.b ∧ ∀ j, 0 ≤ x j

/-- The feasible set `𝒫` is nonempty and bounded (paper: assumption (A2),
`ass:bounded`). Bounded means: all coordinates of all feasible points are bounded
by one common number `R`. -/
def FeasibleSetNonemptyBounded : Prop :=
  (∃ x, P.IsFeasible x) ∧ ∃ R : ℝ, ∀ x, P.IsFeasible x → ∀ j, |x j| ≤ R

/-- `x` is an optimal solution of the LP: feasible, with minimum cost `cᵀx` among
all feasible points. -/
def IsOptimalSolution (x : Fin n → ℝ) : Prop :=
  P.IsFeasible x ∧ ∀ y, P.IsFeasible y → P.c ⬝ᵥ x ≤ P.c ⬝ᵥ y

/-- `B` is a basis: a set of `m` labels such that the square matrix `A_B` is
nonsingular, i.e. (equivalently) the `m` columns `A_j`, `j ∈ B`, are linearly
independent. -/
def IsBasis (B : Finset (Fin n)) : Prop :=
  B.card = m ∧ LinearIndependent ℝ (fun j : B ↦ P.col (j : Fin n))

/-- The defining property of the basic solution `x^B`: `x_j = 0` for every
nonbasic `j ∉ B`, and `Ax = b` (for a basis, equivalent to `x_B = A_B⁻¹ b`). -/
def IsBasicSolutionOf (B : Finset (Fin n)) (x : Fin n → ℝ) : Prop :=
  P.A *ᵥ x = P.b ∧ ∀ j ∉ B, x j = 0

/-- The basic solution `x^B` of a basis `B`: the vector with
`IsBasicSolutionOf B`, which is unique when `B` is a basis. -/
noncomputable def basicSol (B : Finset (Fin n)) : Fin n → ℝ :=
  Classical.epsilon (P.IsBasicSolutionOf B)

/-- `B` is a feasible basis: a basis with `x^B ≥ 0`. -/
def IsFeasibleBasis (B : Finset (Fin n)) : Prop :=
  P.IsBasis B ∧ ∀ j, 0 ≤ P.basicSol B j

/-- The basis `B` is nondegenerate: `x^B_B > 0`, i.e. every basic coordinate of the
basic solution is positive. (Only used for feasible bases.) -/
def IsNondegenerate (B : Finset (Fin n)) : Prop :=
  ∀ i ∈ B, 0 < P.basicSol B i

/-- The objective value `z_B = cᵀx^B` of a basis `B`. -/
noncomputable def objValue (B : Finset (Fin n)) : ℝ :=
  P.c ⬝ᵥ P.basicSol B

/-- `B` is an optimal basis: a feasible basis whose basic solution `x^B` is an
optimal solution of the LP. -/
def IsOptimalBasis (B : Finset (Fin n)) : Prop :=
  P.IsFeasibleBasis B ∧ P.IsOptimalSolution (P.basicSol B)

/-- The defining property of the dual vector `y^B = A_B^{-T} c_B`
(paper: `def:basis_a`): `yᵀA_j = c_j` for every basic label `j ∈ B`. -/
def IsDualVectorOf (B : Finset (Fin n)) (y : Fin m → ℝ) : Prop :=
  ∀ j ∈ B, y ⬝ᵥ P.col j = P.c j

/-- The dual vector `y^B` of a basis `B` (paper: `def:basis_a`). -/
noncomputable def dualVec (B : Finset (Fin n)) : Fin m → ℝ :=
  Classical.epsilon (P.IsDualVectorOf B)

/-- The reduced cost `c̄^B_j = c_j - (y^B)ᵀA_j` of label `j` at the basis `B`
(paper: `def:basis_b`). -/
noncomputable def reducedCost (B : Finset (Fin n)) (j : Fin n) : ℝ :=
  P.c j - P.dualVec B ⬝ᵥ P.col j

/-- The improving set `Γ(B) = {j : c̄^B_j < 0}` of a basis `B`
(paper: `def:basis_c`). -/
noncomputable def improving (B : Finset (Fin n)) : Finset (Fin n) :=
  univ.filter (fun j ↦ P.reducedCost B j < 0)

/-- The defining property of the basic direction `d^{B,j}` for a nonbasic label `j`
(paper: `def:basis_d`): `A d = 0`, `d_j = 1`, and `d_k = 0` for every other
nonbasic label `k ∉ B ∪ {j}`. (For a basis `B`, `A d = 0` with these entries is
equivalent to `d_B = -A_B⁻¹ A_j`.) -/
def IsBasicDirOf (B : Finset (Fin n)) (j : Fin n) (d : Fin n → ℝ) : Prop :=
  P.A *ᵥ d = 0 ∧ d j = 1 ∧ ∀ k, k ∉ B → k ≠ j → d k = 0

/-- The basic direction `d^{B,j}` (paper: `def:basis_d`). -/
noncomputable def basicDir (B : Finset (Fin n)) (j : Fin n) : Fin n → ℝ :=
  Classical.epsilon (P.IsBasicDirOf B j)

/-- `i` is a leaving label of the pivot on `j` at `B`: the basic label `i ∈ B`
attains the minimum in the ratio test
`θ^{B,j} = min { x^B_k / (-d^{B,j}_k) : k ∈ B, d^{B,j}_k < 0 }`
(paper: `def:basis_e`, Equation 2 (`eq:ratio`)). Remark (not part of the definition): under the
paper's assumptions, a leaving label exists and is unique. -/
def IsLeavingLabel (B : Finset (Fin n)) (j i : Fin n) : Prop :=
  i ∈ B ∧ P.basicDir B j i < 0 ∧
    ∀ k ∈ B, P.basicDir B j k < 0 →
      P.basicSol B i / (-P.basicDir B j i) ≤ P.basicSol B k / (-P.basicDir B j k)

/-- `B'` arises from the feasible basis `B` by the pivot on the nonbasic improving
label `j`: `B' = (B \ {i*}) ∪ {j}` for a leaving label `i*`
(paper: text after Equation 3 (`eq:pivot`)). -/
def IsPivot (B : Finset (Fin n)) (j : Fin n) (B' : Finset (Fin n)) : Prop :=
  P.IsFeasibleBasis B ∧ j ∈ P.improving B ∧ j ∉ B ∧
    ∃ i, P.IsLeavingLabel B j i ∧ B' = insert j (B.erase i)

/-- `B 0, B 1, …, B f` is a simplex run (of length `f`) from `B 0`
(paper: definition after Algorithm 1 (`alg:simplex`)): all `B k` are feasible bases,
each `B (k+1)` arises from `B k` by the pivot on some improving label, and the last
basis `B f` has no improving label. Values `B k` for `k > f` are irrelevant. -/
def IsSimplexRun (f : ℕ) (B : ℕ → Finset (Fin n)) : Prop :=
  (∀ k ≤ f, P.IsFeasibleBasis (B k)) ∧
  (∀ k < f, ∃ j ∈ P.improving (B k), P.IsPivot (B k) j (B (k + 1))) ∧
  P.improving (B f) = ∅

end LP

end WolfeSimplex
