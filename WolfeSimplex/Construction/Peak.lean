import WolfeSimplex.Construction.Resources

namespace WolfeSimplex.Construction

open Finset WolfeSimplex.Construction.Computation
variable {m n : ℕ}

private theorem gamma_peak_le (P : IntLP m n) (R : ℕ)
    (hc : P.C.natAbs ≤ R) (hcost : ∀ j, (P.c j).natAbs ≤ R)
    (hg : ∀ j, (P.gamma j).natAbs ≤ R) : (gammaTable P P.C).peak ≤ R := by
  simp only [gammaTable, table_peak, Finset.sup_le_iff]
  intro j _
  have hval : P.C + Fin.snoc (α := fun _ ↦ ℤ) P.c 0 j = P.gamma j := by
    induction j using Fin.lastCases <;> simp [IntLP.gamma]
  change max P.C.natAbs (max (Fin.snoc (α := fun _ ↦ ℤ) P.c 0 j).natAbs
    (P.C + Fin.snoc (α := fun _ ↦ ℤ) P.c 0 j).natAbs) ≤ R
  rw [hval]
  refine max_le hc (max_le ?_ (hg j))
  induction j using Fin.lastCases <;> simp [hcost]

private theorem alpha_peak_le (P : IntLP m n) (R : ℕ)
    (ht : P.T ≤ R) (hu : P.U ≤ P.T) (htu : P.T ^ 2 ≤ R)
    (hb : ∀ i, (P.b i).natAbs ≤ R) (ha : ∀ j i, (P.scaledAlpha j i).natAbs ≤ R) :
    (alphaTable P P.T).peak ≤ R := by
  simp only [alphaTable, table_peak, Finset.sup_le_iff]
  intro j _ i _
  let col := Fin.snoc (α := fun _ ↦ ℤ) (fun k ↦ P.A i k) 0 j
  have hcol : col.natAbs ≤ P.U := by
    induction j using Fin.lastCases <;> simp [col, P.natAbs_A_le]
  have hprod : ((P.T : ℤ) * col).natAbs ≤ R := by
    simp only [Int.natAbs_mul, Int.natAbs_natCast]
    exact (Nat.mul_le_mul_left P.T (hcol.trans hu)).trans (by simpa [pow_two] using htu)
  have hval : (P.T : ℤ) * col - P.b i = P.scaledAlpha j i := by
    induction j using Fin.lastCases <;> simp [col, IntLP.scaledAlpha]
  change max (max ((P.T : ℤ).natAbs) (max col.natAbs ((P.T : ℤ) * col).natAbs))
    (max ((P.T : ℤ) * col).natAbs (max (P.b i).natAbs
      ((P.T : ℤ) * col - P.b i).natAbs)) ≤ R
  rw [hval]
  exact max_le (max_le (by simpa using ht) (max_le (hcol.trans (hu.trans ht)) hprod))
    (max_le hprod (max_le (hb i) (ha j i)))

private theorem output_peak_le (P : IntLP m n) (R : ℕ) (nn q : ℤ)
    (hn : nn.natAbs ≤ R) (hq : q.natAbs ≤ R)
    (hg : ∀ j, (P.gamma j).natAbs ≤ R)
    (ha : ∀ j i, (P.scaledAlpha j i).natAbs ≤ R)
    (hng : ∀ j, (nn * P.gamma j).natAbs ≤ R)
    (hqa : ∀ j i, (q * P.scaledAlpha j i).natAbs ≤ R) :
    (table fun j : Fin (n + 1) ↦ table fun i : Fin (m + 1) ↦
      Fin.cases (mul nn ((Vector.ofFn P.gamma)[j]))
        (fun r ↦ mul q ((Vector.ofFn fun j ↦
          Vector.ofFn (P.scaledAlpha j))[j][r])) i).peak ≤ R := by
  simp only [table_peak, Finset.sup_le_iff]
  intro j _ i _
  induction i using Fin.cases with
  | zero => simpa [mul, binary, max_le_iff] using And.intro (hn) (And.intro (hg j) (hng j))
  | succ i => simpa [mul, binary, max_le_iff] using And.intro (hq) (And.intro (ha j i) (hqa j i))

set_option maxHeartbeats 2000000 in
-- Normalize the complete monitored schedule and its cached integer expressions.
/-- Every integer operand and result is bounded by the same bound already used
for the output coordinates in Lemma 10. -/
theorem run_peak_le (P : IntLP m n) (hm : 1 ≤ m) :
    (run P).peak ≤ P.N ^ 2 * P.K := by
  let R := P.N ^ 2 * P.K
  rcases scalar_bounds P hm with
    ⟨hUT, hmT, h2mT, hmuT, hpowT, hTN, hK2H, hbaseH, hHN, hH3N, hqN, hNR, hTUR, h2R⟩
  have hTR : P.T ≤ R := hTN.trans hNR
  have hUR : P.U ≤ R := hUT.trans hTR
  have hmR : m ≤ R := hmT.trans hTR
  have hm1R : m + 1 ≤ R := by omega
  have hKR : P.K ≤ R := by dsimp [R]; have := P.N_pos hm; nlinarith
  have hHR : P.H ≤ R := hHN.trans hNR
  have hC : P.C.natAbs ≤ P.K := by
    simpa [IntLP.gamma] using P.natAbs_gamma_le (Fin.last n)
  have hmaxc : (univ.sup fun j ↦ (P.c j).natAbs) ≤ P.K := by
    have heq : P.C.natAbs = 1 + (univ.sup fun j ↦ (P.c j).natAbs) := by
      unfold IntLP.C
      change (((1 : ℕ) : ℤ) + ((univ.sup fun j ↦ (P.c j).natAbs : ℕ) : ℤ)).natAbs = _
      rw [← Nat.cast_add, Int.natAbs_natCast]
    rw [heq] at hC
    omega
  have hcR := hC.trans hKR
  have hcost : ∀ j, (P.c j).natAbs ≤ R := fun j ↦
    (Finset.le_sup (mem_univ j)).trans (hmaxc.trans hKR)
  have hgR : ∀ j, (P.gamma j).natAbs ≤ R := fun j ↦ (P.natAbs_gamma_le j).trans hKR
  have haR : ∀ j i, (P.scaledAlpha j i).natAbs ≤ R :=
    fun j i ↦ (P.natAbs_scaledAlpha_le j i).trans hKR
  have hbR : ∀ i, (P.b i).natAbs ≤ R := fun i ↦ (P.natAbs_b_le i).trans hUR
  have hN2R : P.N ^ 2 ≤ R := by dsimp [R]; have := P.one_le_K; nlinarith
  have hT2R : P.T ^ 2 ≤ R := (Nat.pow_le_pow_left hTN 2).trans hN2R
  have hgamma := gamma_peak_le P R hcR hcost hgR
  have halpha := alpha_peak_le P R hTR hUT hT2R hbR haR
  have hmu1 : 1 ≤ (m * P.U) := by have := P.one_le_U; nlinarith
  have hpowPeak : (power ((m : ℤ) * P.U) m).peak ≤ R := by
    have h := power_peak_le (a := (m : ℤ) * P.U)
      (by simpa only [Int.natAbs_mul, Int.natAbs_natCast] using hmu1) m
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using
      h.trans (by simpa only [Int.natAbs_mul, Int.natAbs_natCast] using hpowT.trans hTR)
  have hbase1 : 1 ≤ ((m + 1) * P.K ^ 2) := by
    have := P.one_le_K
    have : 1 ≤ P.K ^ 2 := Nat.one_le_pow _ _ this
    nlinarith
  have hHpeak : (power (((m + 1 : ℕ) : ℤ) * ((P.K : ℤ) * P.K)) (m + 1)).peak ≤ R := by
    have h := power_peak_le (a := ((m + 1 : ℕ) : ℤ) * ((P.K : ℤ) * P.K))
      (by simpa only [Int.natAbs_mul, Int.natAbs_natCast, pow_two] using hbase1) (m + 1)
    have heq : (((m + 1 : ℕ) : ℤ) * ((P.K : ℤ) * P.K)).natAbs ^ (m + 1) = P.H := by
      simp only [Int.natAbs_mul, Int.natAbs_natCast, IntLP.H, pow_two]
    rw [heq] at h
    exact h.trans hHR
  have hHcube : (power (P.H : ℤ) 3).peak ≤ R := by
    have h := power_peak_le (a := (P.H : ℤ)) (by simpa using P.one_le_H) 3
    exact h.trans (by simpa using hH3N.trans hNR)
  have hTval : (2 : ℤ) * m * ((m : ℤ) * P.U) ^ m + 1 = P.T := by simp [IntLP.T]
  have hHval : (((m + 1 : ℕ) : ℤ) * ((P.K : ℤ) * P.K)) ^ (m + 1) = P.H := by
    simp [IntLP.H, pow_two]
  have hNval : (2 : ℤ) * m * (P.H : ℤ) ^ 3 * P.T = P.N := by
    simp [IntLP.N]; ring
  have hcval : (1 : ℤ) + (univ.sup fun j ↦ (P.c j).natAbs : ℕ) = P.C := rfl
  have hupeak : (uScan P).peak ≤ R := by
    change (maxAbs (constraintData P)).peak ≤ R
    rw [maxAbs_peak]
    exact (uScan_value P).le.trans hUR
  have hcpeak : (cScan P).peak ≤ R := by
    change (scanMax (List.ofFn P.c)).peak ≤ R
    rw [scanMax_peak, scanMax_ofFn]
    exact hmaxc.trans hKR
  have hkpeak : (kScan (Vector.ofFn P.gamma)
      (Vector.ofFn fun j ↦ Vector.ofFn (P.scaledAlpha j))).peak ≤ R := by
    change (maxAbs _).peak ≤ R
    rw [maxAbs_peak]
    exact (kScan_value P).le.trans hKR
  have hfactor : P.N * (2 * m * P.H ^ 3) ≤ R :=
    (Nat.mul_le_mul_left P.N hqN).trans (by simpa [pow_two] using hN2R)
  have hng : ∀ j, ((P.N : ℤ) * P.gamma j).natAbs ≤ R := by
    intro j
    rw [Int.natAbs_mul, Int.natAbs_natCast]
    have hg := P.natAbs_gamma_le j
    have hNN : P.N ≤ P.N ^ 2 := by
      calc P.N = P.N * 1 := by ring
           _ ≤ P.N * P.N := Nat.mul_le_mul_left _ (Nat.one_le_iff_ne_zero.mpr (P.N_pos hm).ne')
           _ = _ := by ring
    exact (Nat.mul_le_mul_left P.N hg).trans (Nat.mul_le_mul_right P.K hNN)
  have hqa : ∀ j i, ((P.N : ℤ) * ((2 : ℤ) * m * (P.H : ℤ) ^ 3) *
      P.scaledAlpha j i).natAbs ≤ R := by
    intro j i
    simp only [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_pow, show (2 : ℤ).natAbs = 2 from rfl]
    have ha := P.natAbs_scaledAlpha_le j i
    have hq := hqN
    dsimp [R]
    calc P.N * (2 * m * P.H ^ 3) * (P.scaledAlpha j i).natAbs ≤
        P.N * P.N * P.K := by gcongr
         _ = _ := by ring
  have hout := output_peak_le P R (P.N : ℤ)
    ((P.N : ℤ) * ((2 : ℤ) * m * (P.H : ℤ) ^ 3))
    (by simpa using hNR)
    (by simpa only [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_pow,
      show (2 : ℤ).natAbs = 2 from rfl] using hfactor) hgR haR hng hqa
  have h1R : 1 ≤ R := by omega
  have h2mR := h2mT.trans hTR
  have hmuR := hmuT.trans hTR
  have hpR := hpowT.trans hTR
  have htprodR : 2 * m * (m * P.U) ^ m ≤ R := by
    have : 2 * m * (m * P.U) ^ m ≤ P.T := by simp [IntLP.T]
    exact this.trans hTR
  have hk2R := hK2H.trans hHR
  have hbaseR := hbaseH.trans hHR
  have hcubeR := hH3N.trans hNR
  have hqR := hqN.trans hNR
  -- Expose the monitored operations with their cached mathematical values.
  simp only [run, peak_bind, uScan_value, cScan_value, power_value,
    add, mul, binary, hcval, hTval, gammaTable_value, alphaTable_value, kScan_value,
    hHval, hNval]
  -- Remaining goals are bounds for the scalar operations and output tables.
  simp only [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_pow,
    max_le_iff]
  repeat' apply And.intro
  all_goals first
    | assumption
    | exact hmaxc.trans hKR
    | simpa only [pow_two, R] using hk2R
    | simpa only [pow_two, R] using hbaseR
    | simpa only [mul, binary, Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_pow,
        show (2 : ℤ).natAbs = 2 from rfl] using hout

end WolfeSimplex.Construction
