import WolfeSimplex.Construction.Budget

/-! Control/cell work for the concrete construction, in addition to arithmetic.
The per-cell rates are specified in `Cost` and the three materialization scans in
`Build`. They include dense input traversal and table/list materialization;
the resource monitor itself and compiled runtime remain outside the model. -/

namespace WolfeSimplex.Construction

open Finset WolfeSimplex.Construction.Computation
variable {m n : ℕ}

@[simp] theorem uScan_bookkeeping (P : IntLP m n) :
    (uScan P).bookkeeping = 8 * (m * n + m) + 8 := by
  simp [uScan, constraintData, List.length_flatten, Function.comp_def]; ring

@[simp] theorem cScan_bookkeeping (P : IntLP m n) :
    (cScan P).bookkeeping = 6 * n + 5 := by simp [cScan]; ring

@[simp] theorem gammaTable_bookkeeping (P : IntLP m n) (c : ℤ) :
    (gammaTable P c).bookkeeping = 5 * n + 6 := by simp [gammaTable, add]; ring

@[simp] theorem alphaTable_bookkeeping (P : IntLP m n) (t : ℤ) :
    (alphaTable P t).bookkeeping = 7 * m * (n + 1) + 5 * (n + 1) + 1 := by
  simp [alphaTable, mul, sub]; ring

@[simp] theorem kScan_bookkeeping (g : Vector ℤ (n + 1))
    (a : Vector (Vector ℤ m) (n + 1)) :
    (kScan g a).bookkeeping = 8 * (n + 1) * (m + 1) + 2 := by
  simp [kScan, List.length_flatten, List.map_map, Function.comp_def]; ring

theorem run_bookkeeping (P : IntLP m n) :
    (run P).bookkeeping = 28 * m * n + 32 * m + 34 * n + 85 := by
  simp only [run, bookkeeping_bind, uScan_bookkeeping, cScan_bookkeeping,
    gammaTable_bookkeeping, alphaTable_bookkeeping, kScan_bookkeeping,
    power_bookkeeping, add, mul, binary_bookkeeping, table_bookkeeping]
  simp only [Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ,
    binary_bookkeeping, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

theorem run_work (P : IntLP m n) :
    (run P).work = 35 * m * n + 41 * m + 40 * n + 105 := by
  simp only [work, run_operations, run_bookkeeping]
  ring

/-- Includes arithmetic, control and dense-cell materialization. -/
theorem run_work_le (P : IntLP m n) :
    (run P).work ≤ 150 * (m + n + 1) ^ 2 := by
  simp only [work, run_operations, run_bookkeeping]
  nlinarith

/-- Signed arithmetic width plus a conservative bound for control indices.
Every control index is bounded by the total work of the explicit schedule. -/
def fullWidth (P : IntLP m n) : ℕ := 1 + Nat.size (run P).peak + (run P).work

theorem run_work_input (P : IntLP m n) :
    (run P).work ≤ 1350 * (1 + inputSize P) ^ 2 := by
  have hs := sizeParameter_le P
  have hd : m + n + 1 ≤ 3 * (1 + inputSize P) := by dsimp [sizeParameter] at hs; omega
  calc (run P).work ≤ 150 * (m + n + 1) ^ 2 := run_work_le P
       _ ≤ 150 * (3 * (1 + inputSize P)) ^ 2 := by gcongr
       _ = _ := by ring

theorem fullWidth_input (P : IntLP m n) (hm : 1 ≤ m) :
    fullWidth P ≤ 6000 * (1 + inputSize P) ^ 3 := by
  let L := sizeParameter P
  have hL : 1 ≤ L := by dsimp [L, sizeParameter]; omega
  have hmL : m + 1 ≤ L := by dsimp [L, sizeParameter]; omega
  have hdL : m + n + 1 ≤ L := by dsimp [L, sizeParameter]; omega
  have hbase := base_size_le P
  have hw := run_width_le P hm
  have hop := run_work_le P
  have hwidth : 1 + Nat.size (run P).peak ≤ 1 + 36 * L ^ 3 := by
    apply hw.trans
    calc _ ≤ 1 + 36 * L ^ 2 * L := by gcongr
         _ = _ := by ring
  have hwork : (run P).work ≤ 150 * L ^ 2 := by
    exact hop.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hdL 2))
  have hl2 : L ^ 2 ≤ L ^ 3 := Nat.pow_le_pow_right hL (by omega)
  have hl3 : 1 ≤ L ^ 3 := Nat.one_le_pow _ _ hL
  have hsmall : fullWidth P ≤ 200 * L ^ 3 := by dsimp [fullWidth]; omega
  have hs : L ≤ 3 * (1 + inputSize P) := (sizeParameter_le P).trans (by omega)
  calc fullWidth P ≤ 200 * L ^ 3 := hsmall
       _ ≤ 200 * (3 * (1 + inputSize P)) ^ 3 := by gcongr
       _ ≤ _ := by ring_nf; omega

end WolfeSimplex.Construction
