import WolfeSimplex.Construction.Correctness

namespace WolfeSimplex.Construction

open Finset WolfeSimplex.Construction.Computation
variable {m n : ℕ}

@[simp] theorem binary_operations (f : ℤ → ℤ → ℤ) (a b : ℤ) :
    (binary f a b).operations = 1 := rfl

@[simp] theorem uScan_operations (P : IntLP m n) :
    (uScan P).operations = 2 * (m * n + m) + 1 := by
  simp [uScan, constraintData, List.length_flatten, Function.comp_def]

@[simp] theorem cScan_operations (P : IntLP m n) :
    (cScan P).operations = 2 * n := by simp [cScan]

@[simp] theorem gammaTable_operations (P : IntLP m n) (c : ℤ) :
    (gammaTable P c).operations = n + 1 := by simp [gammaTable, add]

@[simp] theorem alphaTable_operations (P : IntLP m n) (t : ℤ) :
    (alphaTable P t).operations = 2 * m * (n + 1) := by
  simp [alphaTable, mul, sub]
  ring

@[simp] theorem kScan_operations (g : Vector ℤ (n + 1))
    (a : Vector (Vector ℤ m) (n + 1)) :
    (kScan g a).operations = 2 * ((n + 1) + (n + 1) * m) + 1 := by
  simp [kScan, List.length_flatten, List.map_map, Function.comp_def]

/-- Powers use repeated multiplication, and every output product is charged. -/
theorem run_operations (P : IntLP m n) :
    (run P).operations = 7 * m * n + 9 * m + 6 * n + 20 := by
  simp only [run, operations_bind, uScan_operations, cScan_operations,
    gammaTable_operations, alphaTable_operations, kScan_operations, power_operations,
    add, mul, binary_operations, table_operations]
  simp only [Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ,
    binary_operations, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

theorem run_operations_le (P : IntLP m n) :
    (run P).operations ≤ 40 * (m + 1) * (n + 1) := by
  rw [run_operations]
  nlinarith

/-- Bounds for cached constants and temporary products. -/
theorem scalar_bounds (P : IntLP m n) (hm : 1 ≤ m) :
    let r := P.N ^ 2 * P.K
    P.U ≤ P.T ∧ m ≤ P.T ∧ 2 * m ≤ P.T ∧ m * P.U ≤ P.T ∧
    (m * P.U) ^ m ≤ P.T ∧ P.T ≤ P.N ∧ P.K ^ 2 ≤ P.H ∧
    (m + 1) * P.K ^ 2 ≤ P.H ∧ P.H ≤ P.N ∧ P.H ^ 3 ≤ P.N ∧
    2 * m * P.H ^ 3 ≤ P.N ∧ P.N ≤ r ∧ P.T * P.U ≤ r ∧ 2 ≤ r := by
  dsimp only
  have hu := P.one_le_U
  have ht := P.one_le_T
  have hk := P.one_le_K
  have hh := P.one_le_H
  have hn := P.N_pos hm
  have hmu : 1 ≤ m * P.U := by nlinarith
  have hpow : m * P.U ≤ (m * P.U) ^ m := by
    calc m * P.U = (m * P.U) ^ 1 := by simp
         _ ≤ _ := Nat.pow_le_pow_right hmu hm
  have hpow1 : 1 ≤ (m * P.U) ^ m := Nat.one_le_pow _ _ hmu
  have hT : 2 * m * (m * P.U) ^ m + 1 = P.T := rfl
  have hUpow : P.U ≤ m * P.U := by nlinarith
  have hpowT : (m * P.U) ^ m ≤ P.T := by nlinarith
  have hTpos : 2 ≤ P.T := by nlinarith
  have hKsq : 1 ≤ P.K ^ 2 := Nat.one_le_pow _ _ hk
  have hbase : 1 ≤ (m + 1) * P.K ^ 2 := by
    simpa using Nat.mul_le_mul (by omega : 1 ≤ m + 1) hKsq
  have hbaseH : (m + 1) * P.K ^ 2 ≤ P.H := by
    unfold IntLP.H
    calc (m + 1) * P.K ^ 2 = ((m + 1) * P.K ^ 2) ^ 1 := by simp
         _ ≤ _ := Nat.pow_le_pow_right hbase (by omega)
  have hH3 : 1 ≤ P.H ^ 3 := Nat.one_le_pow _ _ hh
  have hN : P.N = 2 * m * P.T * P.H ^ 3 := rfl
  have hTN : P.T ≤ P.N := by
    rw [hN]
    calc P.T = 1 * P.T * 1 := by ring
         _ ≤ _ := by gcongr; omega
  have hHN : P.H ^ 3 ≤ P.N := by
    rw [hN]
    calc P.H ^ 3 = 1 * 1 * P.H ^ 3 := by ring
         _ ≤ _ := by gcongr; omega
  have hHle : P.H ≤ P.H ^ 3 := by
    calc P.H = P.H ^ 1 := by simp
         _ ≤ _ := Nat.pow_le_pow_right hh (by omega)
  have hNR : P.N ≤ P.N ^ 2 * P.K := by nlinarith
  refine ⟨hUpow.trans (hpow.trans hpowT), ?_, ?_, hpow.trans hpowT, hpowT, hTN,
    ?_, hbaseH, hHle.trans hHN, hHN, ?_, hNR, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · have : P.K ^ 2 ≤ (m + 1) * P.K ^ 2 := by nlinarith
    exact this.trans hbaseH
  · rw [hN]
    calc 2 * m * P.H ^ 3 = 2 * m * 1 * P.H ^ 3 := by ring
         _ ≤ _ := by gcongr
  · have hUT := hUpow.trans (hpow.trans hpowT)
    have hUN := hUT.trans hTN
    nlinarith
  · exact hTpos.trans (hTN.trans hNR)

end WolfeSimplex.Construction
