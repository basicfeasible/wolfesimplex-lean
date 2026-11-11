import WolfeSimplex.Construction.Encoding

namespace WolfeSimplex.Construction
open Finset
variable {m n : ℕ}

theorem inputSize_le_width (P : IntLP m n) :
    inputSize P ≤ 10 * (m + n + 1) ^ 2 * (1 + Nat.size P.maxEntry) := by
  have he : ∀ a ∈ inputData P, a.natAbs ≤ P.maxEntry := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · rcases List.mem_append.mp ha with ha | ha
      · obtain ⟨row, hr, ha⟩ := List.mem_flatten.mp ha
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
        obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
        exact (P.natAbs_A_le i j).trans P.U_le_maxEntry
      · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
        exact (P.natAbs_b_le i).trans P.U_le_maxEntry
    · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
      exact (P.natAbs_c_le j).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hl : (inputData P).length = m * n + m + n := by
    simp [inputData, constraintData, List.length_flatten, Function.comp_def]
    omega
  have hp : payloadBits P ≤ (m * n + m + n) * (1 + Nat.size P.maxEntry) := by
    have hh : ∀ xs : List ℤ, (∀ a ∈ xs, a.natAbs ≤ P.maxEntry) →
        (xs.map fun a ↦ 1 + Nat.size a.natAbs).sum ≤ xs.length * (1 + Nat.size P.maxEntry) := by
      intro xs hx
      induction xs with
      | nil => simp
      | cons a xs ih =>
        have ha := Nat.size_le_size (hx a (by simp))
        have ht := ih (fun a ha ↦ hx a (by simp [ha]))
        simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
        omega
    simpa only [payloadBits, hl] using hh (inputData P) he
  have hm : Nat.size m ≤ m := Nat.size_le.mpr Nat.lt_two_pow_self
  have hn : Nat.size n ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  have hd : m * n + m + n + 1 ≤ (m + n + 1) ^ 2 := by nlinarith
  rw [inputSize_eq]
  nlinarith

end WolfeSimplex.Construction
