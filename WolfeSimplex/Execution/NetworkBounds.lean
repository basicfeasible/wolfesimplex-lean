import WolfeSimplex.Execution.Network

/-! Bounds derived from the executed network preprocessing code. -/
namespace WolfeSimplex.Execution.Network
open Code Finset
variable {v m n c : ℕ}

@[simp] theorem equal_size (a b : Code) : (equal a b).size = a.size + b.size + 11 := by
  simp only [equal, size_sub, size_abs, size_sign, Code.size]; omega

theorem select_size (v block row : ℕ) : (select v block row).size ≤ 22 * v + 1 := by
  have h := sum_size_le (List.finRange v)
    (fun w ↦ mul (equal (slot 8 row) (literal w.val)) (slot block w.val)) 19 (by
      intro w _; simp [Code.size])
  simpa [select, List.finRange, List.map_ofFn, Function.comp_def, Nat.mul_comm] using h

private theorem table_size {r : ℕ} (f : Fin r → Code) (b : ℕ)
    (h : ∀ i, (f i).size ≤ b) : (table (List.ofFn f)).size ≤ r * (b + 1) + 1 := by
  simpa only [List.finRange, List.map_ofFn, Function.comp_def, List.length_ofFn] using
    table_size_le (List.finRange r) f b (fun i _ ↦ h i)

theorem code_size (v m n : ℕ) : (code v m n).size ≤ 500 * (v + m + n + 1) ^ 3 := by
  have ha : ∀ r j, (aNum v m n r j).size ≤ 33 := by
    intro r j
    refine Fin.addCases (fun i ↦ ?_) (fun e ↦ ?_) r <;>
      refine Fin.addCases (fun k ↦ ?_) (fun k ↦ ?_) j <;>
      simp [aNum, Code.size, -Fin.natAdd_eq_addNat]
  have hbn : ∀ r, (bNum v m n r).size ≤ 22 * v + 2 := by
    intro r; refine Fin.addCases (fun i ↦ ?_) (fun e ↦ ?_) r <;>
      simp only [bNum, Fin.addCases_left, Fin.addCases_right]
    · exact (select_size v 2 i.val).trans (by omega)
    · change 2 ≤ 22 * v + 2; omega
  have hbd : ∀ r, (bDen v m n r).size ≤ 22 * v + 2 := by
    intro r; refine Fin.addCases (fun i ↦ ?_) (fun e ↦ ?_) r <;>
      simp only [bDen, Fin.addCases_left, Fin.addCases_right]
    · exact (select_size v 3 i.val).trans (by omega)
    · change 2 ≤ 22 * v + 2; omega
  have hcn : ∀ j, (cNum n j).size ≤ 2 := by
    intro j; refine Fin.addCases (fun _ ↦ ?_) (fun _ ↦ ?_) j <;>
      simp [cNum, Code.size, -Fin.natAdd_eq_addNat]
  have hcd : ∀ j, (cDen n j).size ≤ 2 := by
    intro j; refine Fin.addCases (fun _ ↦ ?_) (fun _ ↦ ?_) j <;>
      simp [cDen, Code.size, -Fin.natAdd_eq_addNat]
  have hA := table_size (fun ij : Fin ((m + n) * (n + n)) ↦ aNum v m n ij.divNat ij.modNat)
    33 (fun ij ↦ ha ij.divNat ij.modNat)
  have hD := table_size (fun _ : Fin ((m + n) * (n + n)) ↦ literal 1) 1 (by simp [Code.size])
  have hBN := table_size _ _ hbn
  have hBD := table_size _ _ hbd
  have hCN := table_size _ _ hcn
  have hCD := table_size _ _ hcd
  have ht : (code v m n).size ≤ 36 * ((m + n) * (n + n)) +
      2 * ((m + n) * (22 * v + 3)) + 6 * (n + n) + 11 := by
    simp only [code, Code.size]; nlinarith
  let d := v + m + n + 1
  have hd : 1 ≤ d := by dsimp [d]; omega
  have hr : m + n ≤ d := by dsimp [d]; omega
  have hn : n + n ≤ 2 * d := by dsimp [d]; omega
  have hv : v ≤ d := by dsimp [d]; omega
  have hd3 : d ≤ d ^ 3 := by simpa using Nat.pow_le_pow_right hd (by decide : 1 ≤ 3)
  have h23 : d ^ 2 ≤ d ^ 3 := Nat.pow_le_pow_right hd (by decide)
  have h13 : 1 ≤ d ^ 3 := Nat.one_le_pow _ _ hd
  calc _ ≤ 36 * (d * (2 * d)) + 2 * (d * (22 * d + 3)) + 6 * (2 * d) + 11 :=
        ht.trans (by gcongr)
       _ ≤ 500 * d ^ 3 := by nlinarith

private theorem sign_cert {B f o : ℕ} {a : Code} (h : GrowthCert B f o a) :
    GrowthCert B f o (Code.sign a) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [Code.sign, Code.factor] using h.factor
  · simpa [Code.sign, Code.factor, Code.offset] using h.offset
  · simpa [Code.sign, Code.literalsBounded] using h.literals

private theorem equal_cert {B : ℕ} (hB : 1 ≤ B) {a b : Code}
    (ha : GrowthCert B 1 1 a) (hb : GrowthCert B 1 1 b) :
    GrowthCert B 1 3 (equal a b) := by
  have hs := sign_cert (ha.sub hb)
  have hh := (GrowthCert.literal 1 (by simpa using hB)).sub hs.abs
  simpa [equal] using hh

private theorem table_cert {r B f o : ℕ} (cs : Fin r → Code) (hf : 1 ≤ f)
    (h : ∀ i, GrowthCert B f o (cs i)) : GrowthCert B f o (table (List.ofFn cs)) := by
  simpa only [List.finRange, List.map_ofFn, Function.comp_def] using
    GrowthCert.table (List.finRange r) cs f o hf (fun i _ ↦ h i)

theorem code_growth (v m n B : ℕ) (hB : 1 ≤ B) (hv : v ≤ B) (hn : n ≤ B) :
    GrowthCert B 2 (7 * v + 8) (code v m n) := by
  have lit (k : ℕ) (hk : k ≤ B) : GrowthCert B 1 1 (literal k) :=
    GrowthCert.literal _ (by simpa using hk)
  have sl (block i : ℕ) : GrowthCert B 1 1 (slot block i) :=
    (GrowthCert.slot block i B).mono le_rfl (by omega)
  have heq (a b : Code) (ha : GrowthCert B 1 1 a) (hb : GrowthCert B 1 1 b) :=
    equal_cert hB ha hb
  have hs (block row : ℕ) : GrowthCert B 2 (7 * v + 8) (select v block row) := by
    have hh := GrowthCert.sum (List.finRange v)
      (fun w ↦ mul (equal (slot 8 row) (literal w.val)) (slot block w.val)) 2 6 (by decide)
      (by
        intro w _
        have he := heq _ _ (sl 8 row) (lit w.val (w.isLt.le.trans hv))
        simpa using he.mul (GrowthCert.slot block w.val B))
    simp only [List.length_finRange] at hh
    apply (by simpa [select, List.finRange, List.map_ofFn, Function.comp_def] using hh :
      GrowthCert B 2 (7 * v + 1) (select v block row)).mono le_rfl (by omega)
  have ha : ∀ r j, GrowthCert B 2 (7 * v + 8) (aNum v m n r j) := by
    intro r j
    refine Fin.addCases (fun i ↦ ?_) (fun e ↦ ?_) r
    · refine Fin.addCases (fun e ↦ ?_) (fun e ↦ ?_) j <;>
        simp only [aNum, Fin.addCases_left, Fin.addCases_right]
      · have hh := (heq _ _ (sl 1 e.val) (sl 8 i.val)).sub
          (heq _ _ (sl 0 e.val) (sl 8 i.val))
        exact hh.mono (g := 2) (p := 7 * v + 8) (by simp) (by simp)
      · exact (lit 0 (by omega)).mono (g := 2) (p := 7 * v + 8) (by decide) (by omega)
    · refine Fin.addCases (fun k ↦ ?_) (fun k ↦ ?_) j <;>
        simp only [aNum, Fin.addCases_left, Fin.addCases_right] <;>
        exact (heq _ _ (lit e.val (e.isLt.le.trans hn))
          (lit k.val (k.isLt.le.trans hn))).mono (g := 2) (p := 7 * v + 8) (by decide) (by omega)
  have hbn : ∀ r, GrowthCert B 2 (7 * v + 8) (bNum v m n r) := by
    intro r; refine Fin.addCases (fun i ↦ ?_) (fun e ↦ ?_) r <;>
      simp only [bNum, Fin.addCases_left, Fin.addCases_right]
    · exact hs 2 i.val
    · exact (sl 6 e.val).mono (g := 2) (p := 7 * v + 8) (by decide) (by omega)
  have hbd : ∀ r, GrowthCert B 2 (7 * v + 8) (bDen v m n r) := by
    intro r; refine Fin.addCases (fun i ↦ ?_) (fun e ↦ ?_) r <;>
      simp only [bDen, Fin.addCases_left, Fin.addCases_right]
    · exact hs 3 i.val
    · exact (sl 7 e.val).mono (g := 2) (p := 7 * v + 8) (by decide) (by omega)
  have hcn : ∀ j, GrowthCert B 2 (7 * v + 8) (cNum n j) := by
    intro j; refine Fin.addCases (fun e ↦ ?_) (fun e ↦ ?_) j <;>
      simp only [cNum, Fin.addCases_left, Fin.addCases_right]
    · exact (sl 4 e.val).mono (g := 2) (p := 7 * v + 8) (by decide) (by omega)
    · exact (lit 0 (by omega)).mono (g := 2) (p := 7 * v + 8) (by decide) (by omega)
  have hcd : ∀ j, GrowthCert B 2 (7 * v + 8) (cDen n j) := by
    intro j; refine Fin.addCases (fun e ↦ ?_) (fun e ↦ ?_) j <;>
      simp only [cDen, Fin.addCases_left, Fin.addCases_right]
    · exact (sl 5 e.val).mono (g := 2) (p := 7 * v + 8) (by decide) (by omega)
    · exact (lit 1 hB).mono (g := 2) (p := 7 * v + 8) (by decide) (by omega)
  have hA := table_cert _ (by decide : 1 ≤ 2)
    (fun ij : Fin ((m + n) * (n + n)) ↦ ha ij.divNat ij.modNat)
  have hD := table_cert (fun _ : Fin ((m + n) * (n + n)) ↦ literal 1) (by decide : 1 ≤ 2)
    (fun _ ↦ (lit 1 hB).mono (g := 2) (p := 7 * v + 8) (by decide) (by omega))
  have hBN := table_cert _ (by decide : 1 ≤ 2) hbn
  have hBD := table_cert _ (by decide : 1 ≤ 2) hbd
  have hCN := table_cert _ (by decide : 1 ≤ 2) hcn
  have hCD := table_cert _ (by decide : 1 ≤ 2) hcd
  simpa only [code, max_self] using hA.par (hD.par (hBN.par (hBD.par (hCN.par hCD))))

private theorem equal_address {a b : Code} {R : ℕ} (hR : 1 ≤ R)
    (ha : a.addressBound ≤ R) (hb : b.addressBound ≤ R) :
    (equal a b).addressBound ≤ R := by
  apply address_sub hR (by simpa [Code.addressBound] using hR)
  exact address_abs (address_sign (address_sub hR ha hb))

private theorem table_address {r : ℕ} (cs : Fin r → Code) (R : ℕ)
    (h : ∀ i, (cs i).addressBound ≤ R) : (table (List.ofFn cs)).addressBound ≤ R := by
  apply address_table
  intro c hc
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
  exact h i

theorem code_address (v m n : ℕ) : (code v m n).addressBound ≤ v + m + n + 10 := by
  let R := v + m + n + 10
  have hR : 1 ≤ R := by dsimp [R]; omega
  have lit (k : ℕ) (hk : k ≤ R) : (literal k).addressBound ≤ R := by
    simpa only [Code.addressBound, Int.natAbs_natCast] using hk
  have sl (block i : ℕ) (hb : block ≤ 8) (hi : i ≤ m + n) :
      (slot block i).addressBound ≤ R := address_slot _ _ _ (by dsimp [R]; omega)
        (by dsimp [R]; omega)
  have hs (block row : ℕ) (hb : block ≤ 8) (hi : row ≤ m) :
      (select v block row).addressBound ≤ R := by
    apply address_sum _ R hR
    intro c hc
    obtain ⟨w, rfl⟩ := List.mem_ofFn.mp hc
    apply address_mul hR
    · exact equal_address hR (sl 8 row (by omega) (by omega))
        (lit w.val (by dsimp [R]; have := w.isLt; omega))
    · exact address_slot _ _ _ (by dsimp [R]; omega) (by dsimp [R]; have := w.isLt; omega)
  have ha : ∀ r j, (aNum v m n r j).addressBound ≤ R := by
    intro r j
    refine Fin.addCases (fun i ↦ ?_) (fun e ↦ ?_) r <;>
      refine Fin.addCases (fun k ↦ ?_) (fun k ↦ ?_) j <;>
      simp only [aNum, Fin.addCases_left, Fin.addCases_right]
    · apply address_sub hR
      · exact equal_address hR (sl 1 k.val (by decide) (by have := k.isLt; omega))
          (sl 8 i.val (by decide) (by have := i.isLt; omega))
      · exact equal_address hR (sl 0 k.val (by decide) (by have := k.isLt; omega))
          (sl 8 i.val (by decide) (by have := i.isLt; omega))
    · exact lit 0 (by omega)
    · exact equal_address hR (lit e.val (by dsimp [R]; have := e.isLt; omega))
        (lit k.val (by dsimp [R]; have := k.isLt; omega))
    · exact equal_address hR (lit e.val (by dsimp [R]; have := e.isLt; omega))
        (lit k.val (by dsimp [R]; have := k.isLt; omega))
  have hbn : ∀ r, (bNum v m n r).addressBound ≤ R := by
    intro r; refine Fin.addCases (fun i ↦ ?_) (fun e ↦ ?_) r <;>
      simp only [bNum, Fin.addCases_left, Fin.addCases_right]
    · exact hs 2 i.val (by decide) i.isLt.le
    · exact sl 6 e.val (by decide) (by have := e.isLt; omega)
  have hbd : ∀ r, (bDen v m n r).addressBound ≤ R := by
    intro r; refine Fin.addCases (fun i ↦ ?_) (fun e ↦ ?_) r <;>
      simp only [bDen, Fin.addCases_left, Fin.addCases_right]
    · exact hs 3 i.val (by decide) i.isLt.le
    · exact sl 7 e.val (by decide) (by have := e.isLt; omega)
  have hcn : ∀ j, (cNum n j).addressBound ≤ R := by
    intro j; refine Fin.addCases (fun e ↦ ?_) (fun e ↦ ?_) j <;>
      simp only [cNum, Fin.addCases_left, Fin.addCases_right]
    · exact sl 4 e.val (by decide) (by have := e.isLt; omega)
    · exact lit 0 (by omega)
  have hcd : ∀ j, (cDen n j).addressBound ≤ R := by
    intro j; refine Fin.addCases (fun e ↦ ?_) (fun e ↦ ?_) j <;>
      simp only [cDen, Fin.addCases_left, Fin.addCases_right]
    · exact sl 5 e.val (by decide) (by have := e.isLt; omega)
    · exact lit 1 hR
  have hA := table_address _ R (fun ij : Fin ((m + n) * (n + n)) ↦ ha ij.divNat ij.modNat)
  have hD := table_address (fun _ : Fin ((m + n) * (n + n)) ↦ literal 1) R (fun _ ↦ lit 1 hR)
  have hBN := table_address _ R hbn
  have hBD := table_address _ R hbd
  have hCN := table_address _ R hcn
  have hCD := table_address _ R hcd
  exact max_le hA (max_le hD (max_le hBN (max_le hBD (max_le hCN hCD))))

variable (Q : RationalNetwork v n) (D : Q.toNetwork.RowDeletion m c)

theorem input_bound (B : ℕ) (hv : v ≤ B) (hQ : Q.EntriesBounded B) :
    envBounded (input Q D) B := by
  intro xs hx z hz
  simp only [input, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
  · simpa only [Int.natAbs_natCast] using (Q.tail i).isLt.le.trans hv
  · simpa only [Int.natAbs_natCast] using (Q.head i).isLt.le.trans hv
  · exact (hQ.1 i).1
  · simpa only [Int.natAbs_natCast] using (hQ.1 i).2
  · exact (hQ.2.1 i).1
  · simpa only [Int.natAbs_natCast] using (hQ.2.1 i).2
  · exact (hQ.2.2 i).1
  · simpa only [Int.natAbs_natCast] using (hQ.2.2 i).2
  · simpa only [Int.natAbs_natCast] using (D.rows i).val.isLt.le.trans hv

theorem code_peak : ((code v m n).run (input Q D)).peak ≤
    2 ^ ((Q.inputSize + 1) * (7 * v + 10)) := by
  let B := 2 ^ (Q.inputSize + 1)
  have hd := Q.dimensions_le
  have hB : 2 ≤ B := by
    exact (by norm_num : 2 ≤ 2 ^ 1).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hs : Q.inputSize ≤ B := Nat.lt_two_pow_self.le.trans
    (Nat.pow_le_pow_right (by decide) (by omega))
  have hv : v ≤ B := (by omega : v ≤ Q.inputSize).trans hs
  have hn : n ≤ B := (by omega : n ≤ Q.inputSize).trans hs
  have hg := code_growth v m n B (by omega) hv hn
  have he : envBounded (input Q D) (B ^ 1) := by
    have hb : 2 ^ Q.inputSize ≤ B := Nat.pow_le_pow_right (by decide) (by omega)
    have hh := input_bound Q D (2 ^ Q.inputSize)
      ((by omega : v ≤ Q.inputSize).trans Nat.lt_two_pow_self.le) Q.entries_bounded
    intro xs hx z hz
    simpa only [pow_one] using (hh xs hx z hz).trans hb
  have h := (growth_bound (code v m n) (input Q D) B 1 hB hg.literals he).1
  have hp : (code v m n).factor * 1 + (code v m n).offset ≤ 7 * v + 10 := by
    have hf := hg.factor; have ho := hg.offset; omega
  exact h.trans ((Nat.pow_le_pow_right (by omega) hp).trans (by rw [← pow_mul]))

theorem code_work : ((code v m n).run (input Q D)).work ≤
    10 ^ 9 * (1 + Q.inputSize) ^ 6 := by
  let d := v + m + n + 1
  have hd : 1 ≤ d := by dsimp [d]; omega
  have hs := code_size v m n
  have hw := work_bound (code v m n) (input Q D)
  have hl : (input Q D).length = 9 := by simp [input]
  rw [hl] at hw
  have hc : ((code v m n).run (input Q D)).work ≤ 3000000 * d ^ 6 := by
    have hp : 1 ≤ d ^ 3 := Nat.one_le_pow _ _ hd
    calc _ ≤ 10 * (500 * d ^ 3) * (9 + 500 * d ^ 3 + 1) := hw.trans (by gcongr)
         _ ≤ 3000000 * d ^ 6 := by nlinarith [show d ^ 3 * d ^ 3 = d ^ 6 by rw [← pow_add]]
  have hr := Q.reduced_rows_le D
  have hdim := Q.dimensions_le
  have hds : d ≤ 2 * (1 + Q.inputSize) := by dsimp [d]; omega
  calc _ ≤ 3000000 * (2 * (1 + Q.inputSize)) ^ 6 := hc.trans (Nat.mul_le_mul_left _
          (Nat.pow_le_pow_left hds _))
       _ ≤ 10 ^ 9 * (1 + Q.inputSize) ^ 6 := by rw [mul_pow, ← Nat.mul_assoc]; norm_num

theorem code_bitWork : (code v m n).bitWork (input Q D) ≤
    10 ^ 30 * (1 + Q.inputSize) ^ 20 := by
  let L := 1 + Q.inputSize
  have hL : 1 ≤ L := by dsimp [L]; omega
  have hd := Q.dimensions_le
  have hv : v ≤ L := by dsimp [L]; omega
  have hn : n ≤ L := by dsimp [L]; omega
  have hm : m ≤ L := (Q.reduced_rows_le D).trans hv
  have hwork := code_work Q D
  have hpeak := code_peak Q D
  have hbits : Nat.size ((code v m n).run (input Q D)).peak ≤ 20 * L ^ 2 := by
    have hlt : ((code v m n).run (input Q D)).peak <
        2 ^ ((Q.inputSize + 1) * (7 * v + 10) + 1) := by
      apply hpeak.trans_lt
      rw [pow_succ]; have := pow_pos (by decide : 0 < 2) ((Q.inputSize + 1) * (7 * v + 10)); omega
    have h := Nat.size_le.mpr hlt
    have he : (Q.inputSize + 1) * (7 * v + 10) + 1 ≤ 20 * L ^ 2 := by dsimp [L]; nlinarith
    exact h.trans he
  have haddr : Nat.size (code v m n).addressBound ≤ 20 * L := by
    exact (Nat.size_le.mpr Nat.lt_two_pow_self).trans
      ((code_address v m n).trans (by nlinarith))
  have hctr : Nat.size ((code v m n).run (input Q D)).work ≤ 10 ^ 9 * L ^ 6 :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans hwork
  have h26 : L ^ 2 ≤ L ^ 6 := Nat.pow_le_pow_right hL (by decide)
  have h16 : L ≤ L ^ 6 := by simpa using Nat.pow_le_pow_right hL (by decide : 1 ≤ 6)
  have h06 : 1 ≤ L ^ 6 := Nat.one_le_pow _ _ hL
  have hword : (code v m n).wordWidth (input Q D) ≤ 2000000000 * L ^ 6 := by
    change 1 + Nat.size ((code v m n).run (input Q D)).peak +
      Nat.size (code v m n).addressBound + Nat.size ((code v m n).run (input Q D)).work ≤ _
    nlinarith
  have h18 : L ^ 18 ≤ L ^ 20 := Nat.pow_le_pow_right hL (by decide)
  calc _ ≤ (10 ^ 9 * L ^ 6) * (2000000000 * L ^ 6) ^ 2 :=
        Nat.mul_le_mul hwork (Nat.pow_le_pow_left hword _)
       _ = 4000000000000000000000000000 * L ^ 18 := by ring
       _ ≤ 4000000000000000000000000000 * L ^ 20 := Nat.mul_le_mul_left _ h18
       _ ≤ 10 ^ 30 * L ^ 20 := Nat.mul_le_mul_right _ (by norm_num)

end WolfeSimplex.Execution.Network
