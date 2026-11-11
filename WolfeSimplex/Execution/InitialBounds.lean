import WolfeSimplex.Execution.Canonical
import WolfeSimplex.Execution.BirdPeak
import WolfeSimplex.Execution.Frames
import WolfeSimplex.Proofs.Shield

namespace WolfeSimplex.Execution
open Code Matrix
variable {m n : ℕ}

def preparationBase (P : IntLP m n) : ℕ := 2 * (m + n + 2) * P.maxEntry

private theorem pack_bound {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℤ) (R : ℕ)
    (h : ∀ i j, (M i j).natAbs ≤ R) : ∀ z ∈ pack M, z.natAbs ≤ R := by
  intro z hz
  obtain ⟨ij, rfl⟩ := List.mem_ofFn.mp (by simpa [pack, Matrix.toArray] using hz)
  exact h ij.divNat ij.modNat

private theorem env_cons (xs : List ℤ) (env : Env) (R : ℕ)
    (hx : ∀ z ∈ xs, z.natAbs ≤ R) (he : envBounded env R) : envBounded (xs :: env) R := by
  intro ys hy z hz
  rcases List.mem_cons.mp hy with rfl | hy
  · exact hx z hz
  · exact he ys hy z hz

private theorem input_bound (P : IntLP m n) (R : ℕ) (hR : P.maxEntry ≤ R) :
    envBounded (lpInput P) R := by
  apply env_cons _ _ _ (pack_bound P.A R (fun i j ↦
    (P.natAbs_A_le i j).trans (P.U_le_maxEntry.trans hR)))
  apply env_cons
  · intro z hz
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
    exact (P.natAbs_b_le i).trans (P.U_le_maxEntry.trans hR)
  apply env_cons
  · intro z hz
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hz
    exact (P.natAbs_c_le j).trans (P.sup_c_le_maxEntry.trans hR)
  · intro xs hx
    simp at hx

private theorem replace_bound (P : IntLP m n) (e : Fin m → Fin n) (i j a b : Fin m) :
    (((P.basisMat e).updateRow j (Pi.single i 1)) a b).natAbs ≤ P.maxEntry := by
  rw [Matrix.updateRow_apply]
  split
  · simp only [Pi.single_apply]
    split_ifs <;> simp only [Int.natAbs_one, Int.natAbs_zero]
    · exact (by decide : 1 ≤ 2).trans P.two_le_maxEntry
    · exact Nat.zero_le _
  · exact (P.natAbs_A_le a (e b)).trans P.U_le_maxEntry

private theorem det_bound (P : IntLP m n) (M : Matrix (Fin m) (Fin m) ℤ)
    (hM : ∀ i j, (M i j).natAbs ≤ P.maxEntry) :
    M.det.natAbs ≤ preparationBase P ^ (m + 1) := by
  have hdet := P.abs_det_le_detBd M (fun i j ↦ by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hM i j)
  rw [Int.abs_eq_natAbs] at hdet
  have hd : M.det.natAbs ≤ P.detBd := by exact_mod_cast hdet
  have hbase : (m + 1) * P.maxEntry ≤ preparationBase P := by
    dsimp [preparationBase]
    gcongr
    omega
  exact hd.trans ((P.detBd_le).trans ((Nat.pow_le_pow_left hbase m).trans
    (Nat.pow_le_pow_right (by dsimp [preparationBase]; have := P.two_le_maxEntry; positivity)
      (by omega))))

theorem base_facts (P : IntLP m n) :
    2 ≤ preparationBase P ∧ P.maxEntry ≤ preparationBase P ∧ n + 1 ≤ preparationBase P := by
  have hU := P.two_le_maxEntry
  have hd : 1 ≤ m + n + 2 := by omega
  have hB : P.maxEntry ≤ preparationBase P := by
    dsimp [preparationBase]
    calc _ = 1 * P.maxEntry := by ring
         _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
  refine ⟨hU.trans hB, hB, ?_⟩
  dsimp [preparationBase]
  have hmult := Nat.mul_le_mul_left (2 * (m + n + 2)) hU
  nlinarith

private theorem g_peak (P : IntLP m n) (e : Fin m → Fin n) :
    ((gCode m).run ([(P.basisMat e).det] :: pack (P.basisMat e) :: lpInput P)).peak ≤
      preparationBase P ^ (m + 1) := by
  let B := preparationBase P
  let X := B ^ (m + 1)
  let E := [(P.basisMat e).det] :: pack (P.basisMat e) :: lpInput P
  have hB := (base_facts P).1
  have hB1 : 1 ≤ B := by dsimp [B]; omega
  have hUX : P.maxEntry ≤ X := (base_facts P).2.1.trans (by
    simpa only [pow_one] using Nat.pow_le_pow_right hB1 (by omega : 1 ≤ m + 1))
  have h1X : 1 ≤ X := Nat.one_le_pow _ _ hB1
  have hD := det_bound P (P.basisMat e)
    (fun i j ↦ (P.natAbs_A_le i (e j)).trans P.U_le_maxEntry)
  have hsign : ((P.basisMat e).det.sign).natAbs ≤ 1 := by
    have hs := IntLP.abs_sign_le_one (P.basisMat e).det
    rw [Int.abs_eq_natAbs] at hs
    exact_mod_cast hs
  have hs : ScalarBound X E (sign (slot 0 0)) (P.basisMat e).det.sign := by
    have hv : (slot 0 0).eval E = [(P.basisMat e).det] := rfl
    exact ⟨eval_unary Unary.sign hv,
      scalar_unary_peak Unary.sign X hv (by rw [peak_slot hv]; exact hD) hD
        (hsign.trans h1X), hsign.trans h1X⟩
  apply peak_table
  intro c hc
  obtain ⟨ij, rfl⟩ := List.mem_ofFn.mp hc
  let M := (P.basisMat e).updateRow ij.modNat (Pi.single ij.divNat 1)
  have hM : ∀ a b, (M a b).natAbs ≤ P.maxEntry := replace_bound P e _ _
  have hrow : ((replaceRow m ij.divNat ij.modNat).run E).peak ≤ P.maxEntry := by
    apply peak_table
    intro c hc
    obtain ⟨ab, rfl⟩ := List.mem_ofFn.mp hc
    split_ifs
    · exact (ScalarBound.literal 1 ((by decide : 1 ≤ 2).trans P.two_le_maxEntry)).peak
    · exact (ScalarBound.literal 0 (by simp)).peak
    · have he : (slot 1 (m * ab.divNat.val + ab.modNat.val)).eval E =
          [P.basisMat e ab.divNat ab.modNat] := by
        simp only [eval_slot, E, List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.getD_some]
        exact congrArg (fun z : ℤ ↦ [z]) (pack_get _ _ _)
      exact (ScalarBound.slot _ _ _
        ((P.natAbs_A_le _ _).trans P.U_le_maxEntry) he).peak
  have hdet : ((determinant m).run (pack M :: E)).peak ≤ X := by
    apply (determinant_peak M E P.maxEntry ((by decide : 1 ≤ 2).trans P.two_le_maxEntry) hM).trans
    exact Nat.pow_le_pow_left (by dsimp [preparationBase, B]; gcongr <;> omega) _
  have ht : ScalarBound X E (seq (replaceRow m ij.divNat ij.modNat) (determinant m)) M.det := by
    refine ⟨?_, ?_, det_bound P M hM⟩
    · rw [eval_seq, replaceRow_eval, determinant_correct]
    · rw [peak_seq, replaceRow_eval]
      exact max_le (hrow.trans hUX) hdet
  exact (hs.mul ht (by
    rw [Int.natAbs_mul]
    calc _ ≤ 1 * X := Nat.mul_le_mul hsign ht.magnitude
         _ = X := one_mul _)).peak

/-- The only determinant computations occur in these first three cache stages.
Every original input cell and every resulting cached cell is bounded as well. -/
theorem initial_bounds (P : IntLP m n) (e : Fin m → Fin n) :
    prefixPeak [basisCode e, determinant m, gCode m] (lpInput P) ≤
      preparationBase P ^ (m + 1) ∧
    envBounded (frames [basisCode e, determinant m, gCode m] (lpInput P))
      (preparationBase P ^ (m + 1)) := by
  let B := preparationBase P
  let X := B ^ (m + 1)
  have hB := (base_facts P).1
  have hB1 : 1 ≤ B := by dsimp [B]; omega
  have hUX : P.maxEntry ≤ X := (base_facts P).2.1.trans (by
    simpa only [pow_one] using Nat.pow_le_pow_right hB1 (by omega : 1 ≤ m + 1))
  have hD := det_bound P (P.basisMat e)
    (fun i j ↦ (P.natAbs_A_le i (e j)).trans P.U_le_maxEntry)
  have hb : ((basisCode e).run (lpInput P)).peak ≤ X := by
    apply peak_table
    intro c hc
    obtain ⟨ij, rfl⟩ := List.mem_ofFn.mp hc
    have he : (slot 0 (n * ij.divNat.val + (e ij.modNat).val)).eval (lpInput P) =
        [P.A ij.divNat (e ij.modNat)] := by
      simp only [eval_slot, lpInput, List.getElem?_cons_zero, Option.getD_some]
      exact congrArg (fun z : ℤ ↦ [z]) (pack_get _ _ _)
    exact (ScalarBound.slot _ _ _
      ((P.natAbs_A_le _ _).trans (P.U_le_maxEntry.trans hUX)) he).peak
  have hd : ((determinant m).run (pack (P.basisMat e) :: lpInput P)).peak ≤ X := by
    apply (determinant_peak (P.basisMat e) (lpInput P) P.maxEntry
      ((by decide : 1 ≤ 2).trans P.two_le_maxEntry)
      (fun i j ↦ (P.natAbs_A_le i (e j)).trans P.U_le_maxEntry)).trans
    exact Nat.pow_le_pow_left (by dsimp [preparationBase, B]; gcongr <;> omega) _
  have hG (i j : Fin m) : (P.canonG e i j).natAbs ≤ X := by
    simp only [IntLP.canonG, Matrix.smul_apply, smul_eq_mul, Int.natAbs_mul,
      Matrix.adjugate_apply]
    have hs : ((P.basisMat e).det.sign).natAbs ≤ 1 := by
      have hs := IntLP.abs_sign_le_one (P.basisMat e).det
      rw [Int.abs_eq_natAbs] at hs
      exact_mod_cast hs
    calc _ ≤ 1 * X := Nat.mul_le_mul hs (det_bound P _ (replace_bound P e i j))
         _ = X := one_mul _
  have hbe : (basisCode e).eval (lpInput P) = pack (P.basisMat e) := by
    simpa only [List.append_nil] using basisCode_eval P e []
  simp only [prefixPeak, frames, hbe, determinant_correct, gCode_eval P]
  constructor
  · exact max_le hb (max_le hd (max_le (g_peak P e) (Nat.zero_le _)))
  · apply env_cons _ _ _ (pack_bound _ _ hG)
    apply env_cons
    · simpa only [List.mem_singleton, forall_eq] using hD
    apply env_cons _ _ _ (pack_bound _ _ (fun i j ↦
      (P.natAbs_A_le i (e j)).trans (P.U_le_maxEntry.trans hUX)))
    exact input_bound P X hUX

end WolfeSimplex.Execution
