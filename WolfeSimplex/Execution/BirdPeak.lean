import WolfeSimplex.Execution.Bird
import WolfeSimplex.Execution.ScalarBound

namespace WolfeSimplex.Execution
open Code
variable {n : ℕ}

private theorem cell_bound (A F : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n)
    (env : Env) (U V : ℕ) (hU : 1 ≤ U) (hV : 1 ≤ V)
    (ha : ∀ a b, (A a b).natAbs ≤ U) (hf : ∀ a b, (F a b).natAbs ≤ V) :
    ScalarBound (2 * (n + 1) * U * V) ((pack A ++ pack F) :: env)
      (birdCell n i j) (BirdDet.Spec.stepEntry A F i j) := by
  let E := (pack A ++ pack F) :: env
  let R := 2 * (n + 1) * U * V
  have hUVu : U ≤ U * V := by nlinarith
  have hUVv : V ≤ U * V := by nlinarith
  have hUVR : U * V ≤ R := by dsimp [R]; nlinarith
  have hUR := hUVu.trans hUVR
  have hVR := hUVv.trans hUVR
  have h0 : (0 : ℤ).natAbs ≤ R := by simp
  have ea (a b : Fin n) : (copy (n * a.val + b.val)).eval E = [A a b] := by
    simp only [eval_copy, E, current, List.getElem?_cons_zero, Option.getD_some]
    rw [List.getElem?_append_left (by simpa using (Fin.mkDivMod a b).isLt), pack_get]
  have ef (a b : Fin n) :
      (copy (n * n + n * a.val + b.val)).eval E = [F a b] := by
    simp only [eval_copy, E, current, List.getElem?_cons_zero, Option.getD_some]
    have hi : n * n + n * a.val + b.val = (pack A).length + (n * a.val + b.val) := by
      simp; omega
    rw [hi, List.getElem?_append_right (by omega)]
    simp only [pack_length, Nat.add_sub_cancel_left, pack_get]
  let diag (k : Fin n) : Code :=
    if i < k then copy (n * n + n * k.val + k.val) else literal 0
  let dv (k : Fin n) : ℤ := if i < k then F k k else 0
  have hd (k : Fin n) : ScalarBound V E (diag k) (dv k) := by
    dsimp [diag, dv]
    split
    · exact ScalarBound.copy _ _ (hf k k) (ef k k)
    · exact ScalarBound.literal 0 (by simp)
  let prod (k : Fin n) : Code :=
    if i < k then mul (copy (n * n + n * i.val + k.val)) (copy (n * k.val + j.val))
    else literal 0
  let pv (k : Fin n) : ℤ := if i < k then F i k * A k j else 0
  have hp (k : Fin n) : ScalarBound (U * V) E (prod k) (pv k) := by
    dsimp [prod, pv]
    split
    · apply ScalarBound.mul
        (ScalarBound.copy _ _ ((hf i k).trans hUVv) (ef i k))
        (ScalarBound.copy _ _ ((ha k j).trans hUVu) (ea k j))
      rw [Int.natAbs_mul]
      calc _ ≤ V * U := Nat.mul_le_mul (hf i k) (ha k j)
           _ = _ := by ring
    · exact ScalarBound.literal 0 (by simp)
  have hds := sum_peak (List.finRange n) diag dv E V
    (fun k _ ↦ (hd k).value) (fun k _ ↦ (hd k).peak) (fun k _ ↦ (hd k).magnitude)
  have hps := sum_peak (List.finRange n) prod pv E (U * V)
    (fun k _ ↦ (hp k).value) (fun k _ ↦ (hp k).peak) (fun k _ ↦ (hp k).magnitude)
  simp only [List.length_finRange] at hds hps
  let d := ((List.finRange n).map dv).sum
  let p := ((List.finRange n).map pv).sum
  have hdR : ScalarBound R E (Code.sum ((List.finRange n).map diag)) d :=
    ⟨sum_eval _ _ _ _ (fun k _ ↦ (hd k).value), hds.1.trans (by dsimp [R]; nlinarith),
      hds.2.trans (by dsimp [R]; nlinarith)⟩
  have hpR : ScalarBound R E (Code.sum ((List.finRange n).map prod)) p :=
    ⟨sum_eval _ _ _ _ (fun k _ ↦ (hp k).value), hps.1.trans (by dsimp [R]; nlinarith),
      hps.2.trans (by dsimp [R]; nlinarith)⟩
  have hmul : ((-d) * A i j).natAbs ≤ n * U * V := by
    rw [Int.natAbs_mul, Int.natAbs_neg]
    calc _ ≤ (n * V) * U := Nat.mul_le_mul hds.2 (ha i j)
         _ = _ := by ring
  have hmulR := hmul.trans (by dsimp [R]; nlinarith : n * U * V ≤ R)
  have hsum : ((-d) * A i j + p).natAbs ≤ R := by
    have ht := Int.natAbs_add_le ((-d) * A i j) p
    dsimp [R]
    nlinarith [hps.2]
  have hs := ((hdR.neg.mul (ScalarBound.copy _ _ ((ha i j).trans hUR) (ea i j))
    hmulR).add hpR hsum)
  have hv : (-d) * A i j + p = BirdDet.Spec.stepEntry A F i j :=
    List.cons.inj (hs.value.symm.trans (birdCell_eval A F i j env)) |>.1
  exact ⟨birdCell_eval A F i j env, hs.peak, by rw [← hv]; exact hs.magnitude⟩

private theorem pack_bound {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℤ) (R : ℕ)
    (h : ∀ i j, (M i j).natAbs ≤ R) : ∀ z ∈ pack M, z.natAbs ≤ R := by
  intro z hz
  obtain ⟨ij, rfl⟩ := List.mem_ofFn.mp (by simpa [pack, Matrix.toArray] using hz)
  exact h ij.divNat ij.modNat

private theorem read_peak (is : List ℕ) (env : Env) (xs : List ℤ) (R : ℕ)
    (he : (read is).eval env = xs) (h : ∀ z ∈ xs, z.natAbs ≤ R) :
    ((read is).run env).peak ≤ R := by
  change magnitude ((read is).eval env) ≤ R
  rw [he]
  exact (magnitude_le _ _).mpr h

private theorem first_matrix (A F : Matrix (Fin n) (Fin n) ℤ) (env : Env) :
    (read (List.range (n * n))).eval ((pack A ++ pack F) :: env) = pack A := by
  apply List.ext_getElem
  · simp [eval, run]
  · intro k hk hk'
    simp only [eval, run, current, List.getElem?_cons_zero, Option.getD_some,
      List.getElem_map, List.getElem_range]
    rw [List.getElem?_append_left (by simpa only [Code.length_eval, Code.outputs,
      List.length_range, pack_length] using hk)]
    simp only [List.getElem?_eq_getElem hk', Option.getD_some]

private theorem stage_peak (A F : Matrix (Fin n) (Fin n) ℤ) (env : Env) (U V : ℕ)
    (hU : 1 ≤ U) (hV : 1 ≤ V) (ha : ∀ i j, (A i j).natAbs ≤ U)
    (hf : ∀ i j, (F i j).natAbs ≤ V) :
    ((birdStage n).run ((pack A ++ pack F) :: env)).peak ≤ 2 * (n + 1) * U * V := by
  have hUR : U ≤ 2 * (n + 1) * U * V := by
    calc U ≤ U * V := by nlinarith
         _ ≤ _ := by
           have ht := Nat.mul_le_mul_right (U * V) (by omega : 1 ≤ 2 * (n + 1))
           simpa only [one_mul, mul_assoc] using ht
  simp only [birdStage, peak_par, max_le_iff]
  constructor
  · exact read_peak _ _ _ _ (first_matrix A F env)
      (pack_bound A _ (fun i j ↦ (ha i j).trans hUR))
  · apply peak_table
    intro c hc
    obtain ⟨ij, rfl⟩ := List.mem_ofFn.mp hc
    exact (cell_bound A F _ _ env U V hU hV ha hf).peak

private theorem matrix_iterate_bound (A F : Matrix (Fin n) (Fin n) ℤ) (k U V : ℕ)
    (hU : 1 ≤ U) (hV : 1 ≤ V) (ha : ∀ i j, (A i j).natAbs ≤ U)
    (hf : ∀ i j, (F i j).natAbs ≤ V) :
    ∀ i j, (((BirdDet.Spec.stepEntry A)^[k] F) i j).natAbs ≤
      (2 * (n + 1) * U) ^ k * V := by
  induction k with
  | zero => simpa using hf
  | succ k ih =>
    intro i j
    rw [Function.iterate_succ_apply']
    have hbase : 1 ≤ 2 * (n + 1) * U := by nlinarith
    have hV' : 1 ≤ (2 * (n + 1) * U) ^ k * V :=
      by simpa using Nat.mul_le_mul (Nat.one_le_pow k _ hbase) hV
    have hc := (cell_bound A ((BirdDet.Spec.stepEntry A)^[k] F) i j [] U
      ((2 * (n + 1) * U) ^ k * V) hU hV' ha ih).magnitude
    simpa only [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hc

private theorem iterate_peak (A F : Matrix (Fin n) (Fin n) ℤ) (k : ℕ) (env : Env)
    (U V : ℕ) (hU : 1 ≤ U) (hV : 1 ≤ V) (hUV : U ≤ V)
    (ha : ∀ i j, (A i j).natAbs ≤ U) (hf : ∀ i j, (F i j).natAbs ≤ V) :
    ((iterateCode (birdStage n) k).run ((pack A ++ pack F) :: env)).peak ≤
      (2 * (n + 1) * U) ^ (k + 1) * V := by
  have hbase : 1 ≤ 2 * (n + 1) * U := by nlinarith
  induction k generalizing F V env with
  | zero =>
    simp only [iterateCode, birdStage_outputs]
    have hl : (pack A ++ pack F).length = 2 * (n * n) := by simp; ring
    apply read_peak _ _ _ _ (by rw [← hl, read_range])
    intro z hz
    have hv : z.natAbs ≤ V := by
      rcases List.mem_append.mp hz with hz | hz
      · exact pack_bound A V (fun i j ↦ (ha i j).trans hUV) z hz
      · exact pack_bound F V hf z hz
    exact hv.trans (by simpa only [Nat.zero_add, pow_one] using Nat.le_mul_of_pos_left V hbase)
  | succ k ih =>
    rw [iterateCode, peak_seq, birdStage_eval]
    have hV' : 1 ≤ 2 * (n + 1) * U * V := by simpa using Nat.mul_le_mul hbase hV
    have hVV : V ≤ 2 * (n + 1) * U * V := Nat.le_mul_of_pos_left _ hbase
    have hnext := ih (BirdDet.Spec.stepEntry A F) ((pack A ++ pack F) :: env)
      (2 * (n + 1) * U * V) hV' (hUV.trans hVV)
      (fun i j ↦ (cell_bound A F i j env U V hU hV ha hf).magnitude)
    have he : (2 * (n + 1) * U) ^ (k + 1) * (2 * (n + 1) * U * V) =
        (2 * (n + 1) * U) ^ (k + 1 + 1) * V := by rw [pow_succ]; ring
    rw [he] at hnext
    apply max_le ((stage_peak A F env U V hU hV ha hf).trans ?_) hnext
    calc 2 * (n + 1) * U * V = (2 * (n + 1) * U) ^ 1 * V := by simp
         _ ≤ _ := Nat.mul_le_mul_right V (Nat.pow_le_pow_right hbase (by omega))

/-- Every Bird intermediate has polynomial binary width: its magnitude grows
by at most `2(n+1)U` per stage, across only `n-1` cached stages. -/
theorem determinant_peak (A : Matrix (Fin n) (Fin n) ℤ) (env : Env) (U : ℕ)
    (hU : 1 ≤ U) (ha : ∀ i j, (A i j).natAbs ≤ U) :
    ((determinant n).run (pack A :: env)).peak ≤ (2 * (n + 1) * U) ^ (n + 1) := by
  cases n with
  | zero =>
    simpa [determinant] using (hU.trans (by omega : U ≤ 2 * U))
  | succ k =>
    let B := 2 * (k + 1 + 1) * U
    let R := B ^ (k + 1 + 1)
    have hB : 1 ≤ B := by dsimp [B]; nlinarith
    have hUB : U ≤ B := by dsimp [B]; nlinarith
    have hUR : U ≤ R := hUB.trans (by
      simpa only [pow_one] using Nat.pow_le_pow_right hB (by omega : 1 ≤ k + 1 + 1))
    have hr : (read (List.range ((k + 1) * (k + 1)))).eval (pack A :: env) = pack A := by
      simpa using read_range (pack A) env
    have hp := read_peak _ _ _ U hr (pack_bound A U ha)
    have hi := iterate_peak A A k (pack A :: env) U U hU hU le_rfl ha ha
    have hiR : B ^ (k + 1) * U ≤ R := by
      calc _ ≤ B ^ (k + 1) * B := Nat.mul_le_mul_left _ hUB
           _ = _ := (pow_succ _ _).symm
    have hm := matrix_iterate_bound A A k U U hU hU ha ha
    have hpow : B ^ k * U ≤ R := (Nat.mul_le_mul_right U
      (Nat.pow_le_pow_right hB (by omega : k ≤ k + 1))).trans hiR
    let G := (BirdDet.Spec.stepEntry A)^[k] A
    let E := (pack A ++ pack G) :: (pack A ++ pack A) :: pack A :: env
    have hg : (copy ((k + 1) * (k + 1))).eval E = [G 0 0] := by
      simp only [eval_copy, E, current, List.getElem?_cons_zero, Option.getD_some]
      have he : (k + 1) * (k + 1) = (pack A).length + ((k + 1) * 0 + 0) := by simp
      rw [he, List.getElem?_append_right (by omega)]
      simp only [Nat.add_sub_cancel_left]
      exact congrArg (fun z : ℤ ↦ [z]) (pack_get G 0 0)
    have hsg : ScalarBound R E (copy ((k + 1) * (k + 1))) (G 0 0) :=
      ScalarBound.copy _ _ ((hm 0 0).trans hpow) hg
    have hsign : ((-1 : ℤ) ^ k).natAbs = 1 := by simp [Int.natAbs_pow]
    have hl : ScalarBound R E (literal ((-1 : ℤ) ^ k)) ((-1 : ℤ) ^ k) :=
      ScalarBound.literal _ (by rw [hsign]; exact Nat.one_le_pow _ _ hB)
    have hfinal := (hl.mul hsg (by
      rw [Int.natAbs_mul, hsign, one_mul]
      exact hsg.magnitude)).peak
    simp only [determinant, peak_seq, peak_par, eval_par, hr, bird_iterate]
    exact max_le (max_le (hp.trans hUR) (hp.trans hUR))
      (max_le (hi.trans hiR) hfinal)

end WolfeSimplex.Execution
