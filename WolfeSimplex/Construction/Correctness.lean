import WolfeSimplex.Construction.Build

namespace WolfeSimplex.Construction

open Finset WolfeSimplex.Construction.Computation
variable {m n : ℕ}

@[simp] theorem scanMax_ofFn {r : ℕ} (f : Fin r → ℤ) :
    (scanMax (List.ofFn f)).value = univ.sup (fun i ↦ (f i).natAbs) := by
  apply Nat.le_antisymm
  · apply (scanMax_le_iff _ _).2
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact Finset.le_sup (f := fun i ↦ (f i).natAbs) (mem_univ i)
  · apply Finset.sup_le
    intro i _
    exact (scanMax_le_iff _ _).1 le_rfl _ (List.mem_ofFn.mpr ⟨i, rfl⟩)

@[simp] theorem uScan_value (P : IntLP m n) : (uScan P).value = P.U := by
  apply Nat.le_antisymm
  · apply (maxAbs_le_iff _ _).2
    refine ⟨P.one_le_U, ?_⟩
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨row, hr, ha⟩ := List.mem_flatten.mp ha
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
      exact P.natAbs_A_le i j
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
      exact P.natAbs_b_le i
  · unfold IntLP.U
    apply max_le (by simp [uScan, maxAbs])
    apply max_le
    · apply Finset.sup_le
      rintro ⟨i, j⟩ _
      apply (maxAbs_le_iff _ _).1 le_rfl |>.2
      exact List.mem_append_left _ (List.mem_flatten.mpr
        ⟨_, List.mem_ofFn.mpr ⟨i, rfl⟩, List.mem_ofFn.mpr ⟨j, rfl⟩⟩)
    · apply Finset.sup_le
      intro i _
      apply (maxAbs_le_iff _ _).1 le_rfl |>.2
      exact List.mem_append_right _ (List.mem_ofFn.mpr ⟨i, rfl⟩)

@[simp] theorem cScan_value (P : IntLP m n) :
    (cScan P).value = univ.sup (fun j ↦ (P.c j).natAbs) := scanMax_ofFn _

@[simp] theorem table_value_eq {α : Type} {r : ℕ} (f : Fin r → Computation α) :
    (table f).value = Vector.ofFn (fun i ↦ (f i).value) := by
  apply Vector.ext
  intro i hi
  simp [table]

@[simp] theorem gammaTable_get (P : IntLP m n) (j : Fin (n + 1)) :
    (gammaTable P P.C).value[j] = P.gamma j := by
  induction j using Fin.lastCases <;> simp [gammaTable, add, binary, IntLP.gamma, Fin.snoc]

@[simp] theorem gammaTable_value (P : IntLP m n) :
    (gammaTable P P.C).value = Vector.ofFn P.gamma := by
  apply Vector.ext
  intro j hj
  simpa using gammaTable_get P ⟨j, hj⟩

@[simp] theorem alphaTable_get (P : IntLP m n) (j : Fin (n + 1)) (i : Fin m) :
    (alphaTable P P.T).value[j][i] = P.scaledAlpha j i := by
  induction j using Fin.lastCases <;>
    simp [alphaTable, mul, sub, binary, IntLP.scaledAlpha, Fin.snoc]

@[simp] theorem alphaTable_value (P : IntLP m n) :
    (alphaTable P P.T).value = Vector.ofFn (fun j ↦ Vector.ofFn (P.scaledAlpha j)) := by
  apply Vector.ext
  intro j hj
  apply Vector.ext
  intro i hi
  simpa using alphaTable_get P ⟨j, hj⟩ ⟨i, hi⟩

@[simp] theorem kScan_value (P : IntLP m n) :
    (kScan (Vector.ofFn P.gamma)
      (Vector.ofFn (fun j ↦ Vector.ofFn (P.scaledAlpha j)))).value = P.K := by
  simp only [kScan, materialize_value, Vector.toList_ofFn, List.map_ofFn, Function.comp_def]
  apply Nat.le_antisymm
  · apply (maxAbs_le_iff _ _).2
    refine ⟨P.one_le_K, ?_⟩
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
      exact P.natAbs_gamma_le j
    · obtain ⟨row, hr, ha⟩ := List.mem_flatten.mp ha
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hr
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
      exact P.natAbs_scaledAlpha_le j i
  · unfold IntLP.K
    apply Finset.sup_le
    intro j _
    have hspec := (maxAbs_le_iff _ _).1
      (le_rfl : (maxAbs (List.ofFn P.gamma ++
        (List.ofFn fun j ↦ List.ofFn (P.scaledAlpha j)).flatten)).value ≤ _)
    refine max_le (hspec.2 _ ?_) (max_le ?_ hspec.1)
    · exact List.mem_append_left _ (List.mem_ofFn.mpr ⟨j, rfl⟩)
    · apply Finset.sup_le
      intro i _
      exact hspec.2 _ (List.mem_append_right _ (List.mem_flatten.mpr
        ⟨_, List.mem_ofFn.mpr ⟨j, rfl⟩, List.mem_ofFn.mpr ⟨i, rfl⟩⟩))

/-- The executable construction equals the real atoms, coordinate by coordinate. -/
theorem atoms_correct (P : IntLP m n) (j : Fin (n + 1)) (i : Fin (m + 1)) :
    ((atoms P)[j][i] : ℝ) = P.atom j i := by
  have ht : (2 : ℤ) * m * ((m : ℤ) * P.U) ^ m + 1 = P.T := by
    simp [IntLP.T]
  have hc : (1 : ℤ) + (univ.sup fun j ↦ (P.c j).natAbs : ℕ) = P.C := rfl
  simp only [atoms, run, value_bind, power_value, uScan_value, cScan_value, add, mul, binary,
    hc, ht, gammaTable_value, alphaTable_value, kScan_value]
  induction i using Fin.cases with
  | zero =>
    simp [table, IntLP.atom_zero, IntLP.N, IntLP.H]
    ring_nf
    simp
  | succ i =>
    rw [IntLP.atom_succ, IntLP.N_sq_mul_alpha]
    simp [table, IntLP.N, IntLP.H]
    ring_nf
    simp

end WolfeSimplex.Construction
