import WolfeSimplex.Efficiency.PivotPlan

/-!
# Polynomial closure lemmas for internal procedure summaries

The public execution theorem is `MachineAlgorithm.corollary1` in MachineTransfer.
The paper's iteration formulation is `corollary1_iterations` in RuleIterations.
These closure lemmas use internal report summaries. Their hypotheses include rule evaluation,
exact arithmetic and history/control work. The induced procedure is executable
relative to that supplied procedure. Strong polynomiality bounds total arithmetic
and control/cell work independently of coefficient magnitudes; numerical widths
remain polynomial in the binary input length.
-/

namespace WolfeSimplex.Efficiency

open WolfeSimplex.Construction

private theorem construction_work_bits :
    PolynomialBound sourceSize (fun i ↦ (run i.lp).work) :=
  ⟨1350, 2, fun i ↦ run_work_input i.lp⟩

private theorem construction_work_dimension :
    PolynomialBound sourceDimension (fun i ↦ (run i.lp).work) := by
  refine ⟨150, 2, fun i ↦ ?_⟩
  have hd : i.m + i.n + 1 ≤ 1 + sourceDimension i := by
    dsimp [sourceDimension]; omega
  exact (run_work_le i.lp).trans
    (Nat.mul_le_mul_left 150 (Nat.pow_le_pow_left hd 2))

private theorem construction_width_bits :
    PolynomialBound sourceSize (fun i ↦ fullWidth i.lp) :=
  ⟨6000, 3, fun i ↦ fullWidth_input i.lp i.admissible.1⟩

theorem source_dimension_bits : PolynomialBound sourceSize sourceDimension := by
  refine ⟨3, 1, fun i ↦ ?_⟩
  have h := sizeParameter_le i.lp
  dsimp [sizeParameter] at h
  dsimp [sourceDimension, sourceSize]
  simp only [pow_one]
  omega

/-- Polynomial growth of the reduction's full target input. -/
theorem reduction_input_size :
    PolynomialBound sourceSize (fun i ↦ targetSize (reduce i)) := by
  refine ⟨24300, 5, fun i ↦ ?_⟩
  have h := pointSize_atoms i.lp i.admissible
  change pointSize (atoms i.lp) ≤ _
  convert h using 1; dsimp [sourceSize]; ring

/-- Only two dimensions increase by one; coefficient widths do not enter. -/
theorem reduction_dimension :
    PolynomialBound sourceDimension (fun i ↦ targetDimension (reduce i)) := by
  refine ⟨1, 1, fun i ↦ ?_⟩
  simp only [targetDimension, reduce, sourceDimension, pow_one, one_mul]
  omega

private theorem wrapper_work {s : Source → ℕ} (A : WolfeProcedure)
    (hc : PolynomialBound s (fun i ↦ (run i.lp).work))
    (hd : PolynomialBound s sourceDimension)
    (ha : PolynomialBound s (fun i ↦ (A (reduce i)).work)) :
    PolynomialBound s (fun i ↦ (induce A i).work) := by
  exact (hc.add (((PolynomialBound.const s 20).mul hd).mul
    (ha.add (PolynomialBound.const s 1)))).mono (induce_work A)

private theorem wrapper_width (A : WolfeProcedure)
    (ha : PolynomialBound sourceSize (fun i ↦ (A (reduce i)).width))
    (hw : PolynomialBound sourceSize (fun i ↦ (induce A i).work)) :
    PolynomialBound sourceSize (fun i ↦ (induce A i).width) := by
  exact ((((PolynomialBound.const sourceSize 1).add construction_width_bits).add ha).add hw).mono
    (induce_width A)

/-- Ordinary polynomial time in the specified arithmetic/array bit-cost model. -/
theorem polynomial_transfer (A : WolfeProcedure) (hA : PolynomialWolfe A) :
    PolynomialSimplex (induce A) := by
  have ha := hA.work.comp reduce reduction_input_size
  have hb := hA.width.comp reduce reduction_input_size
  have hw := wrapper_work A construction_work_bits source_dimension_bits ha
  exact ⟨induce_correct A hA.correct, hw, wrapper_width A hb hw⟩

/-- Strong polynomiality: work depends only on dimensions, and intermediate
numerical representations have polynomial binary length in the source input. -/
theorem strongly_polynomial_transfer (A : WolfeProcedure) (hA : StronglyPolynomialWolfe A) :
    StronglyPolynomialSimplex (induce A) := by
  have ha := hA.work.comp reduce reduction_dimension
  have hb := hA.width.comp reduce reduction_input_size
  have hw := wrapper_work A construction_work_dimension
    (PolynomialBound.input sourceDimension) ha
  have hwb := hw.comp id source_dimension_bits
  exact ⟨induce_correct A hA.correct, hw, wrapper_width A hb hwb⟩

/-- Corollary 1, with one common induced procedure for both efficiency notions. -/
theorem corollary1 (A : WolfeProcedure) :
    (PolynomialWolfe A → PolynomialSimplex (induce A)) ∧
    (StronglyPolynomialWolfe A → StronglyPolynomialSimplex (induce A)) :=
  ⟨polynomial_transfer A, strongly_polynomial_transfer A⟩

/-- Polynomial work and width give a polynomial bit charge for the whole wrapper. -/
theorem polynomial_bit_work (A : SimplexProcedure) (hA : PolynomialSimplex A) :
    PolynomialBound sourceSize (fun i ↦ (A i).bitWork) :=
  hA.work.mul hA.width.square

/-- Strongly polynomial work also yields ordinary polynomial bit cost. -/
theorem strongly_polynomial_bit_work (A : SimplexProcedure) (hA : StronglyPolynomialSimplex A) :
    PolynomialBound sourceSize (fun i ↦ (A i).bitWork) :=
  (hA.work.comp id source_dimension_bits).mul hA.width.square

end WolfeSimplex.Efficiency
