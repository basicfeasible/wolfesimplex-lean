import WolfeSimplex.Construction.Peak
import WolfeSimplex.Construction.Encoding

/-!
# Polynomial arithmetic bit budget for the executable construction

The bound uses the length of `inputEncoding`, including dimensions and all dense
integer entries. It charges integer arithmetic, absolute values and comparisons.
Table/list allocation, indexing, loop control and the resource monitor itself are
outside the model. This is not a compiled-runtime or Turing-machine theorem.
-/

namespace WolfeSimplex.Construction

open WolfeSimplex.Construction.Computation
variable {m n : ℕ}

/-- Every monitored operand/result has polynomial signed binary length. -/
theorem run_width_le (P : IntLP m n) (hm : 1 ≤ m) :
    1 + Nat.size (run P).peak ≤
      1 + 36 * (m + 1) ^ 2 * Nat.size ((m + 1) * P.maxEntry) := by
  apply Nat.add_le_add_left
  have h := IntLP.magnitude_bits_le (z := ((run P).peak : ℤ))
    (b := (m + 1) * P.maxEntry) (e := 36 * (m + 1) ^ 2) (by positivity)
  apply h
  simpa only [Int.natAbs_natCast] using (run_peak_le P hm).trans (P.N_sq_mul_K_le hm)

/-- A direct dimension-and-coefficient-width budget. -/
theorem run_bitBudget_le (P : IntLP m n) (hm : 1 ≤ m) :
    (run P).bitBudget ≤ 40 * (m + 1) * (n + 1) *
      (1 + 36 * (m + 1) ^ 2 * Nat.size ((m + 1) * P.maxEntry)) ^ 2 := by
  exact Nat.mul_le_mul (run_operations_le P)
    (Nat.pow_le_pow_left (run_width_le P hm) 2)

/-- Polynomial in a compact parameter that includes dimensions and coefficient width. -/
theorem run_bitBudget_parameter (P : IntLP m n) (hm : 1 ≤ m) :
    (run P).bitBudget ≤ 54760 * sizeParameter P ^ 8 := by
  let L := sizeParameter P
  have hL : 1 ≤ L := by dsimp [L, sizeParameter]; omega
  have hmL : m + 1 ≤ L := by dsimp [L, sizeParameter]; omega
  have hnL : n + 1 ≤ L := by dsimp [L, sizeParameter]; omega
  have hqL : Nat.size ((m + 1) * P.maxEntry) ≤ L := base_size_le P
  have hL3 : 1 ≤ L ^ 3 := Nat.one_le_pow _ _ hL
  have hwidth : 1 + 36 * (m + 1) ^ 2 * Nat.size ((m + 1) * P.maxEntry) ≤ 37 * L ^ 3 := by
    calc _ ≤ 1 + 36 * L ^ 2 * L := by gcongr
         _ ≤ 37 * L ^ 3 := by nlinarith [hL3]
  calc (run P).bitBudget ≤ 40 * (m + 1) * (n + 1) *
        (1 + 36 * (m + 1) ^ 2 * Nat.size ((m + 1) * P.maxEntry)) ^ 2 :=
          run_bitBudget_le P hm
       _ ≤ 40 * L * L * (37 * L ^ 3) ^ 2 := by gcongr
       _ = _ := by dsimp [L]; ring

/-- Polynomial in the length of an explicit dense binary input encoding. -/
theorem run_bitBudget_input (P : IntLP m n) (hm : 1 ≤ m) :
    (run P).bitBudget ≤ 54760 * (3 * inputSize P) ^ 8 := by
  exact (run_bitBudget_parameter P hm).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (sizeParameter_le P) 8))

/-- A single entry point: executable output correctness, exact arithmetic count,
intermediate magnitude bound, and polynomial arithmetic bit budget. -/
theorem certificate (P : IntLP m n) (hm : 1 ≤ m) :
    (∀ (j : Fin (n + 1)) (i : Fin (m + 1)),
      ((atoms P)[j][i] : ℝ) = P.atom j i) ∧
    (run P).operations = 7 * m * n + 9 * m + 6 * n + 20 ∧
    (run P).peak ≤ P.N ^ 2 * P.K ∧
    (run P).bitBudget ≤ 54760 * (3 * inputSize P) ^ 8 :=
  ⟨atoms_correct P, run_operations P, run_peak_le P hm, run_bitBudget_input P hm⟩

end WolfeSimplex.Construction
