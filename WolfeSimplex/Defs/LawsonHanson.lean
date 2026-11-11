import WolfeSimplex.Defs.Wolfe

/-!
# Nonnegative least squares and the Lawson–Hanson algorithm (paper: Appendix C.3 (`app:nnls`))

Trusted definitions for Appendix C.3 (`app:nnls`): the NNLS problem
`min ‖Eν − f‖ subject to ν ≥ 0` (Equation 37 (`eq:nnls`)), the reduction of Lawson and Hanson from
the atoms `p_j` (the matrix with the columns `(p_j, 1)ᵀ` and `f = (0, 1)ᵀ`), and the
Lawson–Hanson algorithm [LH74, Algorithm (23.10)] as described in the paragraph
"The Lawson–Hanson algorithm".

## How the algorithm is modeled

A state consists of the set `F`, the vector `ν`, and the *phase*: `outer` (at the
beginning of an outer iteration, where `r = Eᵀ(f − Eν)` is computed) or `inner` (in
the inner loop, where the least-squares vector `ζ` on `F` is computed). One `Step`
is one of:

* `add`: in phase `outer`, a label `j ∉ F` with `r_j > 0` that maximizes `r_j` over
  `j ∉ F` is added to `F` (any maximizer: ties may be broken arbitrarily); the phase
  becomes `inner`.
* `accept`: in phase `inner`, if `ζ_i > 0` for all `i ∈ F`, then `ν ← ζ`; the phase
  becomes `outer` (the outer iteration ends).
* `innerIter`: in phase `inner`, if `ζ_i ≤ 0` for some `i ∈ F`, then
  `ν ← ν + ϑ(ζ − ν)` with `ϑ = min {ν_i/(ν_i − ζ_i) : i ∈ F, ζ_i ≤ 0}`, and every
  label `i` with new `ν_i = 0` is removed from `F` (an *inner iteration*).

The algorithm stops in phase `outer` when `r_j ≤ 0` for all `j ∉ F`. An execution
starts at `F = ∅`, `ν = 0`, phase `outer`. The number of outer iterations that add
a label is the number of `add` steps, i.e. the number of `outer` states before the
last state.
-/

namespace WolfeSimplex

namespace LH

open Finset Matrix

variable {d n : ℕ} (E : Matrix (Fin d) (Fin n) ℝ) (f : Fin d → ℝ)

/-- The squared residual `‖Eν − f‖²`. -/
def resSq (ν : Fin n → ℝ) : ℝ := (E *ᵥ ν - f) ⬝ᵥ (E *ᵥ ν - f)

/-- The defining property of the least-squares vector on `F`: `ζ` vanishes outside
`F` and minimizes `‖Eζ − f‖` among all vectors that vanish outside `F`. -/
def IsLsSolOf (F : Finset (Fin n)) (ζ : Fin n → ℝ) : Prop :=
  (∀ i ∉ F, ζ i = 0) ∧ ∀ ζ' : Fin n → ℝ, (∀ i ∉ F, ζ' i = 0) → resSq E f ζ ≤ resSq E f ζ'

/-- The least-squares vector `ζ` on `F` (unique if the columns `E_i`, `i ∈ F`, are
linearly independent, which is the case in every state reached in our results). -/
noncomputable def lsSol (F : Finset (Fin n)) : Fin n → ℝ :=
  Classical.epsilon (IsLsSolOf E f F)

/-- The vector `r = Eᵀ(f − Eν)` (the negative gradient of `‖Eν − f‖²/2`). -/
def resid (ν : Fin n → ℝ) : Fin n → ℝ := Eᵀ *ᵥ (f - E *ᵥ ν)

/-- The phase of a state of the Lawson–Hanson algorithm. -/
inductive Phase
  | /-- at the beginning of an outer iteration -/ outer
  | /-- inside the inner loop -/ inner
  deriving DecidableEq

/-- A state of the Lawson–Hanson algorithm: the phase, the set `F`, and the vector `ν`. -/
structure State (n : ℕ) where
  /-- the phase -/
  phase : Phase
  /-- the current set `F` -/
  F : Finset (Fin n)
  /-- the current vector `ν` -/
  nu : Fin n → ℝ

/-- The initial state: phase `outer`, `F = ∅`, `ν = 0`. -/
def init : State n := ⟨.outer, ∅, 0⟩

/-- `ϑ` is the step length `min {ν_i/(ν_i − ζ_i) : i ∈ F, ζ_i ≤ 0}` of an inner
iteration: it is one of these ratios, and at most each of them. (Lean's convention
`x/0 = 0` would give the ratio `0` if `ν_i = ζ_i = 0`; this case does not occur in
the executions considered here.) -/
def IsInnerStep (F : Finset (Fin n)) (ν ζ : Fin n → ℝ) (ϑ : ℝ) : Prop :=
  (∃ i ∈ F, ζ i ≤ 0 ∧ ϑ = ν i / (ν i - ζ i)) ∧
  ∀ i ∈ F, ζ i ≤ 0 → ϑ ≤ ν i / (ν i - ζ i)

/-- An `add` step: in phase `outer`, a label `j ∉ F` with `r_j > 0` that maximizes
`r_j` over the labels not in `F` is added to `F`; the phase becomes `inner`. -/
def AddStep (j : Fin n) (s s' : State n) : Prop :=
  s.phase = .outer ∧ j ∉ s.F ∧ 0 < resid E f s.nu j ∧
    (∀ k ∉ s.F, resid E f s.nu k ≤ resid E f s.nu j) ∧
    s' = ⟨.inner, insert j s.F, s.nu⟩

/-- An `accept` step: in phase `inner`, if the least-squares vector `ζ` on `F` is
positive on `F`, then `ν ← ζ`, and the phase becomes `outer`. -/
def AcceptStep (s s' : State n) : Prop :=
  s.phase = .inner ∧ (∀ i ∈ s.F, 0 < lsSol E f s.F i) ∧
    s' = ⟨.outer, s.F, lsSol E f s.F⟩

/-- An inner iteration: in phase `inner`, if `ζ_i ≤ 0` for some `i ∈ F`, then
`ν ← ν + ϑ(ζ − ν)` with `ϑ = min {ν_i/(ν_i − ζ_i) : i ∈ F, ζ_i ≤ 0}`, and every label
`i` with new `ν_i = 0` is removed from `F`. -/
def InnerStep (s s' : State n) : Prop :=
  s.phase = .inner ∧ (∃ i ∈ s.F, lsSol E f s.F i ≤ 0) ∧
    ∃ ϑ, IsInnerStep s.F s.nu (lsSol E f s.F) ϑ ∧
      s' = ⟨.inner, s.F.filter (fun i ↦ s.nu i + ϑ * (lsSol E f s.F i - s.nu i) ≠ 0),
        s.nu + ϑ • (lsSol E f s.F - s.nu)⟩

/-- One step of the Lawson–Hanson algorithm: an `add` step (for some label), an
`accept` step, or an inner iteration. -/
def Step (s s' : State n) : Prop :=
  (∃ j, AddStep E f j s s') ∨ AcceptStep E f s s' ∨ InnerStep E f s s'

/-- The algorithm stops at `s`: phase `outer` and `r_j ≤ 0` for all `j ∉ F`. -/
def IsStopped (s : State n) : Prop :=
  s.phase = .outer ∧ ∀ j ∉ s.F, resid E f s.nu j ≤ 0

/-- `s 0, …, s T` is a partial execution of the Lawson–Hanson algorithm (`T` steps
from the initial state; the last state need not be a stopping state). -/
def IsPartialExecution (T : ℕ) (s : ℕ → State n) : Prop :=
  s 0 = init ∧ ∀ k < T, Step E f (s k) (s (k + 1))

/-- `s 0, …, s T` is an execution of the Lawson–Hanson algorithm: a partial
execution that ends in a stopping state. -/
def IsExecution (T : ℕ) (s : ℕ → State n) : Prop :=
  IsPartialExecution E f T s ∧ IsStopped E f (s T)

/-- The number of outer iterations that add a label among the first `T` steps: the
number of `k < T` such that `s k` is in phase `outer` (the step from an `outer`
state is always an `add` step). -/
noncomputable def numAdds (T : ℕ) (s : ℕ → State n) : ℕ :=
  ((range T).filter fun k ↦ (s k).phase = .outer).card

/-- The sets `F` of the states in phase `outer` among `s 0, …, s T`, in order. -/
noncomputable def outerSets (T : ℕ) (s : ℕ → State n) : List (Finset (Fin n)) :=
  ((List.range (T + 1)).filter fun k ↦ (s k).phase = .outer).map fun k ↦ (s k).F

/-- The sets of labels added by the `add` steps among the first `T` steps, in order:
for every `k < T` in phase `outer`, the set `F(s (k+1)) \ F(s k)` (a singleton `{j}`
for the added label `j`). -/
noncomputable def addedSets (T : ℕ) (s : ℕ → State n) : List (Finset (Fin n)) :=
  ((List.range T).filter fun k ↦ (s k).phase = .outer).map fun k ↦ (s (k + 1)).F \ (s k).F

end LH

/-- The matrix of the reduction of Lawson and Hanson (paper: Equation 37 (`eq:nnls`)): the column of
`j` is `(p_j, 1)ᵀ` (the coordinates of `p_j` first, then the entry `1`). The
right-hand side is `f = (0, 1)ᵀ`, i.e. `nnlsRhs`. -/
def nnlsMatrix {n D : ℕ} (p : Fin n → Fin D → ℝ) : Matrix (Fin (D + 1)) (Fin n) ℝ :=
  Matrix.of fun r j ↦ Fin.snoc (α := fun _ ↦ ℝ) (p j) 1 r

/-- The right-hand side `f = (0, 1)ᵀ ∈ ℝ^{D+1}` of the reduction (paper: Equation 37 (`eq:nnls`)).
-/
def nnlsRhs (D : ℕ) : Fin (D + 1) → ℝ := Fin.snoc (α := fun _ ↦ ℝ) 0 1

end WolfeSimplex
