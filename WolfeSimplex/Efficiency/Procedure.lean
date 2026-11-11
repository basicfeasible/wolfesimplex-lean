import WolfeSimplex.Efficiency.InputSize
import WolfeSimplex.Efficiency.Polynomial

/-!
# Costed complete procedures and the induced simplex procedure

The hypothetical Wolfe procedure is supplied with its FULL execution cost:
selection, exact numerical work, state/history maintenance and control. An output
trace charge is mandatory. The wrapper runs it once and reads off the simplex
bases. No simplex linear-system calculation is needed in the wrapper.

This is a relative algorithm theorem in a specified array-arithmetic cost model.
It neither asserts the existence of an efficient Wolfe rule nor verifies a compiler.
-/

namespace WolfeSimplex.Efficiency

open WolfeSimplex.Construction
variable {m n : ℕ}

/-- Internal execution summaries for the polynomial closure lemmas. The public
`MachineAlgorithm.procedure` derives these fields from primitive execution. Raw
reports alone are not execution certificates. `bodyWork` represents complete work;
`numberBits` bounds signed numerical representations.
The public cost also charges output cells and traversal, even if bodyWork is zero. -/
structure Report (N : ℕ) where
  trace : List (Mask N)
  bodyWork : ℕ
  numberBits : ℕ

namespace Report
variable {N : ℕ}

def work (r : Report N) : ℕ := 1 + r.bodyWork + (N + 1) * r.trace.length
/-- Include control indices/counters as well as the reported numerical width. -/
def width (r : Report N) : ℕ := 1 + r.numberBits + Nat.size r.work
/-- Uniform quadratic bit charge for all work in the arithmetic model. -/
def bitWork (r : Report N) : ℕ := r.work * r.width ^ 2

theorem length_le_work (r : Report N) : r.trace.length ≤ r.work := by
  dsimp [work]; nlinarith

theorem width_le (r : Report N) : r.width ≤ 1 + r.numberBits + r.work := by
  have hs : Nat.size r.work ≤ r.work := Nat.size_le.mpr Nat.lt_two_pow_self
  dsimp [width]; omega
end Report

/-- Valid inputs are represented concretely; proof fields are erased at runtime. -/
structure Source where
  m : ℕ
  n : ℕ
  lp : IntLP m n
  initial : Mask n
  admissible : lp.IsAdmissible
  feasible : lp.toLP.IsFeasibleBasis (support initial)

structure Target where
  N : ℕ
  D : ℕ
  points : Points N D
  initial : Mask N
  corral : Wolfe.IsCorral (realPoints points) (support initial)

def sourceSize (i : Source) : ℕ := inputSize i.lp
def sourceDimension (i : Source) : ℕ := i.m + i.n + 1
def targetSize (i : Target) : ℕ := pointSize i.points
def targetDimension (i : Target) : ℕ := i.N + i.D

abbrev WolfeProcedure := (i : Target) → Report i.N
abbrev SimplexProcedure := (i : Source) → Report i.n

def CorrectWolfe (A : WolfeProcedure) : Prop :=
  ∀ i, WolfeTrace (realPoints i.points) i.initial (A i).trace

def CorrectSimplex (A : SimplexProcedure) : Prop :=
  ∀ i, SimplexTrace i.lp i.initial (A i).trace

structure PolynomialWolfe (A : WolfeProcedure) : Prop where
  correct : CorrectWolfe A
  work : PolynomialBound targetSize (fun i ↦ (A i).work)
  width : PolynomialBound targetSize (fun i ↦ (A i).width)

structure StronglyPolynomialWolfe (A : WolfeProcedure) : Prop where
  correct : CorrectWolfe A
  work : PolynomialBound targetDimension (fun i ↦ (A i).work)
  width : PolynomialBound targetSize (fun i ↦ (A i).width)

structure PolynomialSimplex (A : SimplexProcedure) : Prop where
  correct : CorrectSimplex A
  work : PolynomialBound sourceSize (fun i ↦ (A i).work)
  width : PolynomialBound sourceSize (fun i ↦ (A i).width)

structure StronglyPolynomialSimplex (A : SimplexProcedure) : Prop where
  correct : CorrectSimplex A
  work : PolynomialBound sourceDimension (fun i ↦ (A i).work)
  width : PolynomialBound sourceSize (fun i ↦ (A i).width)

@[simp] theorem realPoints_atoms (P : IntLP m n) : realPoints (atoms P) = P.atom := by
  funext j i
  exact atoms_correct P j i

/-- Construct the integer Wolfe input, with the corresponding starting support. -/
def reduce (i : Source) : Target where
  N := i.n + 1
  D := i.m + 1
  points := atoms i.lp
  initial := start i.initial
  corral := by
    rw [realPoints_atoms, support_start]
    exact (PaperPath.part_a i.lp i.admissible _ i.feasible).1

/-- Concrete wrapper. The extra per-frame charge includes projecting the support,
reading its entering label and emitting the simplex trace. The complete Wolfe
execution, including any history and exact linear algebra, is charged in `A`. -/
def induce (A : WolfeProcedure) (i : Source) : Report i.n :=
  let t : Report (i.n + 1) := A (reduce i)
  let projected := projectTrace t.trace
  { trace := projected.value
    bodyWork := (run i.lp).work + t.work + 3 * (i.n + 1) + projected.work +
      8 * (i.n + 1) * t.trace.length
    numberBits := fullWidth i.lp + t.width }

theorem induce_correct (A : WolfeProcedure) (hA : CorrectWolfe A) :
    CorrectSimplex (induce A) := by
  intro i
  apply project_correct i.lp i.admissible i.initial i.feasible
  simpa only [reduce, realPoints_atoms] using hA (reduce i)

/-- No step or history length is treated as free in the simulation overhead. -/
theorem induce_work (A : WolfeProcedure) (i : Source) :
    (induce A i).work ≤ (run i.lp).work +
      20 * sourceDimension i * ((A (reduce i)).work + 1) := by
  let t : Report (i.n + 1) := A (reduce i)
  have hlen : t.trace.length ≤ t.work := t.length_le_work
  change 1 + ((run i.lp).work + t.work + 3 * (i.n + 1) +
    (projectTrace t.trace).work + 8 * (i.n + 1) * t.trace.length) +
    (i.n + 1) * (projectTrace t.trace).value.length ≤
    (run i.lp).work + 20 * sourceDimension i * (t.work + 1)
  rw [projectTrace_work, projectTrace_value, List.length_map]
  have hmul := Nat.mul_le_mul_left (11 * (i.n + 1)) hlen
  dsimp [sourceDimension]
  nlinarith

theorem induce_width (A : WolfeProcedure) (i : Source) :
    (induce A i).width ≤ 1 + fullWidth i.lp + (A (reduce i)).width + (induce A i).work := by
  have h := Report.width_le (induce A i)
  convert h using 1; simp only [induce, Report.width, Report.work, reduce]; ring

end WolfeSimplex.Efficiency
