import WolfeSimplex.Efficiency.Machine
import WolfeSimplex.Execution.Budget

/-!
# Corollary 1 for measured complete procedures

The LP-to-point constructor and the supplied Wolfe program are executed in their
primitive semantics. Their common input/output arrays are proved equal below.
The closed wrapper projects the support trace; it grants no uncharged numerical
work to the supplied algorithm. Iteration-only rules are handled separately in
`RuleIterations`, matching the paper's major-cycle formulation.
-/
namespace WolfeSimplex.Efficiency
open Execution

/-- The exact point-array frame passed to the Wolfe machine is the output of
the first-order constructor. This is the data-flow link for the staged wrapper. -/
theorem reduction_input_executed (i : Source) :
    targetData (reduce i) = (atomCode i.m i.n).eval (lpInput i.lp) := by
  have hv : (atomCode i.m i.n).eval (lpInput i.lp) = pack (integerAtoms i.lp) := by
    simpa only [List.append_nil] using atomCode_correct i.lp []
  rw [hv]
  have hm : integerAtoms i.lp = fun j k ↦ (Construction.atoms i.lp)[j][k] := by
    funext j k
    apply Int.cast_injective (α := ℝ)
    rw [integerAtoms_correct, Construction.atoms_correct]
  rw [hm]
  simp only [targetData, reduce, pack, Matrix.toArray, Array.toList_ofFn]
  congr 1

def constructorWork (i : Source) : ℕ := ((atomCode i.m i.n).run (lpInput i.lp)).work

def constructorWidth (i : Source) : ℕ :=
  1 + Nat.size ((atomCode i.m i.n).run (lpInput i.lp)).peak +
    Nat.size (atomCode i.m i.n).addressBound + Nat.size (constructorWork i)

private theorem constructor_work_dimension :
    PolynomialBound sourceDimension constructorWork := by
  refine ⟨2000000, 4, fun i ↦ ?_⟩
  exact (atomCode_work i.lp).trans (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_left (by dsimp [sourceDimension]; omega) 4))

private theorem constructor_work_bits : PolynomialBound sourceSize constructorWork :=
  constructor_work_dimension.comp id source_dimension_bits

private theorem constructor_width_bits : PolynomialBound sourceSize constructorWidth := by
  refine ⟨10000000000, 4, fun i ↦ ?_⟩
  have hb := atom_wordWidth i.lp i.admissible.1
  have hs : Construction.sizeParameter i.lp ≤ 3 * sourceSize i :=
    Construction.sizeParameter_le i.lp
  change (atomCode i.m i.n).wordWidth (lpInput i.lp) ≤ _
  calc _ ≤ 2001637 * Construction.sizeParameter i.lp ^ 4 := hb
       _ ≤ 2001637 * (3 * (1 + sourceSize i)) ^ 4 := by gcongr; omega
       _ ≤ _ := by ring_nf; omega

namespace MachineAlgorithm

/-- The staged induced execution: construct the point array once, execute the
Wolfe machine, and project its emitted supports. All metrics are derived from
these fixed components; no caller supplies a work or width report. -/
noncomputable def induce (A : MachineAlgorithm) (i : Source) : Report i.n :=
  let t := A.procedure (reduce i)
  let projected := projectTrace t.trace
  { trace := projected.value
    bodyWork := constructorWork i + t.work + 3 * (i.n + 1) + projected.work +
      8 * (i.n + 1) * t.trace.length
    numberBits := constructorWidth i + t.width }

private theorem work_le (A : MachineAlgorithm) (i : Source) :
    (A.induce i).work ≤ (Efficiency.induce A.procedure i).work + constructorWork i := by
  dsimp only [induce, Efficiency.induce, Report.work, reduce]
  omega

private theorem width_le (A : MachineAlgorithm) (i : Source) :
    (A.induce i).width ≤ 1 + constructorWidth i + (Efficiency.induce A.procedure i).width +
      (A.induce i).work := by
  have hw := Report.width_le (A.induce i)
  have ht : (A.procedure (reduce i)).width ≤ (Efficiency.induce A.procedure i).width := by
    dsimp only [Efficiency.induce, Report.width, reduce]
    omega
  dsimp only [induce, reduce] at hw ht ⊢
  omega

theorem induce_correct (A : MachineAlgorithm) (hA : CorrectWolfe A.procedure) :
    CorrectSimplex A.induce := by
  intro i
  exact Efficiency.induce_correct A.procedure hA i

/-- Ordinary polynomial work and numerical width, for executed procedures. -/
theorem polynomial_transfer (A : MachineAlgorithm) (hA : PolynomialWolfe A.procedure) :
    PolynomialSimplex A.induce := by
  have old := Efficiency.polynomial_transfer A.procedure hA
  have hw := (old.work.add constructor_work_bits).mono A.work_le
  have hb := ((((PolynomialBound.const sourceSize 1).add constructor_width_bits).add
    old.width).add hw).mono A.width_le
  exact ⟨A.induce_correct hA.correct, hw, hb⟩

/-- Strong polynomiality measures work by dimensions and numerical widths by
binary input length, including literal addresses and control counters. -/
theorem strongly_polynomial_transfer (A : MachineAlgorithm)
    (hA : StronglyPolynomialWolfe A.procedure) : StronglyPolynomialSimplex A.induce := by
  have old := Efficiency.strongly_polynomial_transfer A.procedure hA
  have hw := (old.work.add constructor_work_dimension).mono A.work_le
  have hwb := hw.comp id source_dimension_bits
  have hb := ((((PolynomialBound.const sourceSize 1).add constructor_width_bits).add
    old.width).add hwb).mono A.width_le
  exact ⟨A.induce_correct hA.correct, hw, hb⟩

/-- Corollary 1, with a common induced procedure and interpreter-derived costs. -/
theorem corollary1 (A : MachineAlgorithm) :
    (PolynomialWolfe A.procedure → PolynomialSimplex A.induce) ∧
    (StronglyPolynomialWolfe A.procedure → StronglyPolynomialSimplex A.induce) :=
  ⟨A.polynomial_transfer, A.strongly_polynomial_transfer⟩

/-- Reviewer entry point: constructor-to-machine data agreement, a genuine
halting machine execution, and both running-time implications together. -/
theorem certificate (A : MachineAlgorithm) :
    (∀ i : Source, targetData (reduce i) = (atomCode i.m i.n).eval (lpInput i.lp)) ∧
    (∀ i : Target, Execution.execute A.program (A.fuel i) (machineInput i) = some (A.result i)) ∧
    (PolynomialWolfe A.procedure → PolynomialSimplex A.induce) ∧
    (StronglyPolynomialWolfe A.procedure → StronglyPolynomialSimplex A.induce) :=
  ⟨reduction_input_executed, A.executed, A.corollary1⟩

end MachineAlgorithm
end WolfeSimplex.Efficiency
