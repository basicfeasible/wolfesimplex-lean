import WolfeSimplex.Execution.Shield

/-! Uniform syntax/work bounds for preparation programs. Coefficient magnitudes
never control program generation, branching or the number of executed stages. -/
namespace WolfeSimplex.Execution
open Code
variable {m n : ℕ}


private theorem table_fin_size {r : ℕ} (f : Fin r → Code) (b : ℕ)
    (h : ∀ i, (f i).size ≤ b) : (table (List.ofFn f)).size ≤ r * (b + 1) + 1 := by
  have ht := table_size_le (List.finRange r) f b (fun i _ ↦ h i)
  simpa only [List.finRange, List.map_ofFn, Function.comp_def, List.length_ofFn] using ht

theorem birdCell_size (n : ℕ) (i j : Fin n) : (birdCell n i j).size ≤ 20 * (n + 1) := by
  have hd := sum_size_le (List.finRange n)
    (fun k ↦ if i < k then copy (n * n + n * k.val + k.val) else literal 0) 2
    (by intro k _; split <;> simp [size])
  have hp := sum_size_le (List.finRange n)
    (fun k ↦ if i < k then mul (copy (n * n + n * i.val + k.val))
      (copy (n * k.val + j.val)) else literal 0) 7
    (by intro k _; split <;> simp [size])
  simp only [List.length_finRange] at hd hp
  simp only [birdCell, size_add, size_mul, size_neg, size_copy]
  omega

theorem birdStage_size (n : ℕ) : (birdStage n).size ≤ 25 * (n + 1) ^ 3 := by
  have ht := table_fin_size (fun ij : Fin (n * n) ↦ birdCell n ij.divNat ij.modNat)
    (20 * (n + 1)) (fun _ ↦ birdCell_size _ _ _)
  simp only [birdStage, size, List.length_range]
  nlinarith

/-- Division-free determinant work is polynomial, even though a determinant's
Leibniz expansion would have factorially many terms. -/
theorem determinant_size (n : ℕ) : (determinant n).size ≤ 100 * (n + 1) ^ 4 := by
  cases n with
  | zero => norm_num [determinant, size]
  | succ k =>
    have hs := birdStage_size (k + 1)
    have hsk := Nat.mul_le_mul_left k hs
    simp only [determinant, size, List.length_range, iterateCode_size, birdStage_outputs,
      size_mul, size_copy]
    nlinarith

private theorem basisCode_size (e : Fin m → Fin n) :
    (basisCode e).size ≤ 3 * m ^ 2 + 1 := by
  have h := table_fin_size
    (fun ij : Fin (m * m) ↦ slot 0 (n * ij.divNat.val + (e ij.modNat).val)) 2 (by simp)
  simpa only [basisCode, pow_two, Nat.mul_comm] using h

private theorem replaceRow_size (i j : Fin m) : (replaceRow m i j).size ≤ 3 * m ^ 2 + 1 := by
  have h := table_fin_size (fun ab : Fin (m * m) ↦
    if ab.divNat = j then literal (if ab.modNat = i then 1 else 0)
    else slot 1 (m * ab.divNat.val + ab.modNat.val)) 2
    (by intro ab; split <;> simp [size])
  simpa only [replaceRow, pow_two, Nat.mul_comm] using h

private theorem gCode_size (m : ℕ) : (gCode m).size ≤ 200 * (m + 1) ^ 6 := by
  have h := table_fin_size
    (fun ij : Fin (m * m) ↦ mul (sign (slot 0 0))
      (seq (replaceRow m ij.divNat ij.modNat) (determinant m)))
    (3 * m ^ 2 + 100 * (m + 1) ^ 4 + 9) (by
      intro ij
      have hr := replaceRow_size ij.divNat ij.modNat
      have hd := determinant_size m
      simp only [size_mul, size_sign, size_slot, size]
      omega)
  change (gCode m).size ≤ _ at h
  apply h.trans
  ring_nf
  omega

private theorem canonicalA_size (m n : ℕ) :
    (canonicalA m n).size ≤ m * n * (10 * m + 2) + 1 := by
  apply table_fin_size
  intro ij
  have hs := sum_size_le (List.finRange m)
    (fun k ↦ mul (slot 0 (m * ij.divNat.val + k.val)) (slot 3 (n * k.val + ij.modNat.val)))
    7 (by simp)
  simpa only [List.length_finRange, Nat.reduceAdd, Nat.mul_comm] using hs

private theorem canonicalB_size (m : ℕ) :
    (canonicalB m).size ≤ m * (10 * m + 6) + 1 := by
  apply table_fin_size
  intro i
  have hs := sum_size_le (List.finRange m)
    (fun k ↦ mul (slot 1 (m * i.val + k.val)) (slot 5 k.val)) 7 (by simp)
  simp only [List.length_finRange] at hs
  simp only [size_mul, size]
  omega

private theorem canonicalC_size (e : Fin m → Fin n) :
    (canonicalC e).size ≤ n * (10 * m + 14) + 1 := by
  apply table_fin_size
  intro j
  have hs := sum_size_le (List.finRange m)
    (fun i ↦ mul (slot 1 (n * i.val + j.val)) (slot 7 (e i).val)) 7 (by simp)
  simp only [List.length_finRange] at hs
  simp only [size_sub, size_mul, size_abs, size_slot]
  omega

theorem canonicalCode_size (e : Fin m → Fin n) (body : Code) :
    (canonicalCode e body).size ≤ 1000 * (m + n + 2) ^ 6 + body.size := by
  let d := m + n + 2
  have hd : 1 ≤ d := by dsimp [d]; omega
  have hm : m ≤ d := by dsimp [d]; omega
  have hn : n ≤ d := by dsimp [d]; omega
  have hm1 : m + 1 ≤ d := by dsimp [d]; omega
  have hb : (basisCode e).size ≤ 4 * d ^ 2 := by
    calc _ ≤ 3 * m ^ 2 + 1 := basisCode_size e
         _ ≤ 3 * d ^ 2 + 1 := by gcongr
         _ ≤ _ := by nlinarith [Nat.one_le_pow 2 d hd]
  have hdet : (determinant m).size ≤ 100 * d ^ 4 :=
    (determinant_size m).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hm1 4))
  have hg : (gCode m).size ≤ 200 * d ^ 6 :=
    (gCode_size m).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hm1 6))
  have ha : (canonicalA m n).size ≤ 13 * d ^ 3 := by
    calc _ ≤ m * n * (10 * m + 2) + 1 := canonicalA_size m n
         _ ≤ d * d * (10 * d + 2) + 1 := by gcongr
         _ ≤ _ := by nlinarith [Nat.one_le_pow 2 d hd]
  have hbb : (canonicalB m).size ≤ 17 * d ^ 2 := by
    calc _ ≤ m * (10 * m + 6) + 1 := canonicalB_size m
         _ ≤ d * (10 * d + 6) + 1 := by gcongr
         _ ≤ _ := by nlinarith
  have hc : (canonicalC e).size ≤ 25 * d ^ 2 := by
    calc _ ≤ n * (10 * m + 14) + 1 := canonicalC_size e
         _ ≤ d * (10 * d + 14) + 1 := by gcongr
         _ ≤ _ := by nlinarith
  have h2 := Nat.pow_le_pow_right hd (by decide : 2 ≤ 6)
  have h3 := Nat.pow_le_pow_right hd (by decide : 3 ≤ 6)
  have h4 := Nat.pow_le_pow_right hd (by decide : 4 ≤ 6)
  have hb' := hb.trans (Nat.mul_le_mul_left 4 h2)
  have hd' := hdet.trans (Nat.mul_le_mul_left 100 h4)
  have ha' := ha.trans (Nat.mul_le_mul_left 13 h3)
  have hbb' := hbb.trans (Nat.mul_le_mul_left 17 h2)
  have hc' := hc.trans (Nat.mul_le_mul_left 25 h2)
  have hone := Nat.one_le_pow 6 d hd
  change (canonicalCode e body).size ≤ 1000 * d ^ 6 + body.size
  simp only [canonicalCode, size]
  omega

private theorem nonbasicMax_size (e : Fin m → Fin n) (f : Fin n → Code) (b : ℕ)
    (h : ∀ j, (f j).size ≤ b) : (nonbasicMax e f).size ≤ n * (b + 7) + 1 := by
  have ht := maxList_size_le (List.finRange n)
    (fun j ↦ if j ∈ basisOf e then literal 0 else positive (f j)) (b + 4) (by
      intro j _
      split
      · simp [size]
      · simp only [positive, size_max, size]
        have := h j
        omega)
  simpa only [nonbasicMax, List.length_finRange, Nat.add_assoc, Nat.reduceAdd] using ht

private theorem coefficient_size (e : Fin m → Fin n) :
    (shieldCoefficient e).size ≤ n * (14 * m + 8) + 8 := by
  have hn := nonbasicMax_size e (fun j ↦ Code.sum ((List.finRange m).map fun i ↦
    mul (slot 1 i.val) (max (slot 2 (n * i.val + j.val)) (literal 0)))) (14 * m + 1) (by
      intro j
      have hs := sum_size_le (List.finRange m)
        (fun i ↦ mul (slot 1 i.val) (max (slot 2 (n * i.val + j.val)) (literal 0)))
        11 (by simp [size])
      simpa only [List.length_finRange, Nat.reduceAdd, Nat.mul_comm] using hs)
  simp only [Nat.add_assoc, Nat.reduceAdd] at hn
  simp only [shieldCoefficient, size_add, size_abs, size_slot]
  omega

private theorem weight_size (e : Fin m → Fin n) :
    (shieldWeight e).size ≤ n * (10 * m + 8) + 6 := by
  have hn := nonbasicMax_size e (fun j ↦ Code.sum ((List.finRange m).map fun i ↦
    mul (slot 3 (n * i.val + j.val)) (slot 3 (n * i.val + j.val)))) (10 * m + 1) (by
      intro j
      have hs := sum_size_le (List.finRange m)
        (fun i ↦ mul (slot 3 (n * i.val + j.val)) (slot 3 (n * i.val + j.val)))
        7 (by simp)
      simpa only [List.length_finRange, Nat.reduceAdd, Nat.mul_comm] using hs)
  simp only [Nat.add_assoc, Nat.reduceAdd] at hn
  simp only [shieldWeight, size_add, size_slot]
  omega

private theorem shieldMatrix_size (e : Fin m → Fin n) :
    (shieldMatrix e).size ≤ (m + 1) * (n + 1) * 5 + 1 := by
  apply table_fin_size _ 4
  intro ij
  simp only [shieldEntry]
  split_ifs <;> simp [size]

private theorem weightedMatrix_size (e : Fin m → Fin n) (σ : Equiv.Perm (Fin n)) :
    (weightedMatrix e σ).size ≤ (m + 1) * (n + 1) * 9 + 1 := by
  apply table_fin_size _ 8
  intro ij
  simp only [weightedEntry]
  split_ifs <;> simp [size]

private theorem finishShield_size (m n : ℕ) :
    (finishShield m n).size ≤ 2000 * (m + n + 2) ^ 2 := by
  have ha := atomCode_size (m + 1) (n + 1)
  simp only [finishShield, size, List.length_range]
  nlinarith

/-- The entire unweighted shortest-start program has polynomial syntax size. -/
theorem shieldCode_size (e : Fin m → Fin n) :
    (shieldCode e).size ≤ 10000 * (m + n + 2) ^ 6 := by
  have hc := canonicalCode_size e (extend (shieldCoefficient e) (extend (shieldWeight e)
    (extend (shieldMatrix e) (finishShield m n))))
  have ha := coefficient_size e
  have hw := weight_size e
  have hm := shieldMatrix_size e
  have hf := finishShield_size m n
  simp only [size] at hc
  change (shieldCode e).size ≤ _ at hc
  have hpoly : 1000 * (m + n + 2) ^ 6 +
      (n * (14 * m + 8) + 8) + (n * (10 * m + 8) + 6) +
      ((m + 1) * (n + 1) * 5 + 1) + 2000 * (m + n + 2) ^ 2 + 3 ≤
      10000 * (m + n + 2) ^ 6 := by ring_nf; omega
  omega

/-- The weighted construction has the same polynomial bound, uniformly over
all basis enumerations and permutations of the original labels. -/
theorem weightedCode_size (e : Fin m → Fin n) (σ : Equiv.Perm (Fin n)) :
    (weightedCode e σ).size ≤ 10000 * (m + n + 2) ^ 6 := by
  have hc := canonicalCode_size e (extend (shieldCoefficient e) (extend (shieldWeight e)
    (extend (weightedMatrix e σ) (finishShield m n))))
  have ha := coefficient_size e
  have hw := weight_size e
  have hm := weightedMatrix_size e σ
  have hf := finishShield_size m n
  simp only [size] at hc
  change (weightedCode e σ).size ≤ _ at hc
  have hpoly : 1000 * (m + n + 2) ^ 6 +
      (n * (14 * m + 8) + 8) + (n * (10 * m + 8) + 6) +
      ((m + 1) * (n + 1) * 9 + 1) + 2000 * (m + n + 2) ^ 2 + 3 ≤
      10000 * (m + n + 2) ^ 6 := by ring_nf; omega
  omega

/-- Actual executed arithmetic, control and cell work. This bound applies
uniformly to both preparation programs and is independent of coefficients. -/
theorem preparation_work (P : IntLP m n) (c : Code)
    (hs : c.size ≤ 10000 * (m + n + 2) ^ 6) :
    (c.run (lpInput P)).work ≤ 1100000000 * (m + n + 2) ^ 12 := by
  have hw := work_bound c (lpInput P)
  have hp : 1 ≤ (m + n + 2) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have hlen : (lpInput P).length = 3 := rfl
  rw [hlen] at hw
  calc _ ≤ 10 * (10000 * (m + n + 2) ^ 6) * (3 + 10000 * (m + n + 2) ^ 6 + 1) :=
          hw.trans (by gcongr)
       _ ≤ _ := by
         rw [show 12 = 6 * 2 from rfl, pow_mul]
         nlinarith [sq_nonneg ((m + n + 2) ^ 6)]

end WolfeSimplex.Execution
