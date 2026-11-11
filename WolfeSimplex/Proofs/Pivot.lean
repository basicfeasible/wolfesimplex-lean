import WolfeSimplex.Proofs.Hat

/-!
# One major cycle is one pivot (paper: Step 4, Lemma 6 (`lem:pivot`)), and Theorem 1
(`thm:equivalence`)

The proof follows the proof of Lemma 6 (`lem:pivot`) in the paper: after inserting `j`
at the corral `B̂`, the affine minimizer of `B̂ ∪ {j}` is the origin with
coefficients `μ = λ^{B̂} + τ d^{B̂,j}` (`τ = h/(-c̄_j)`), the coefficient of the
leaving label `i*` becomes zero first, and every other coefficient stays positive
by the bounds of Lemma 5 (`lem:bases-corrals`).
-/

namespace WolfeSimplex.IntLP

open Finset Matrix Wolfe

variable {m n : ℕ} {P : IntLP m n} {B : Finset (Fin n)}

/-! ### Part (a) -/

lemma rcHat_castSucc (k : Fin n) : P.rcHat B (Fin.castSucc k) = P.toLP.reducedCost B k := by
  simp [rcHat]

lemma rcHat_last : P.rcHat B (Fin.last n) = 0 := by
  simp [rcHat]

lemma kappa_pos (hB : P.toLP.IsFeasibleBasis B) (hm : 1 ≤ m) :
    0 < (P.N : ℝ) ^ 4 * P.eps B := by
  have := P.N_pos' hm
  have := eps_pos hB hm
  positivity

lemma improving_hat (hB : P.toLP.IsFeasibleBasis B) (hm : 1 ≤ m) :
    improving P.atom (affineMin P.atom (hat B)) = (P.toLP.improving B).map Fin.castSuccEmb := by
  have hκ := kappa_pos hB hm
  ext k
  simp only [Wolfe.improving, mem_filter, mem_univ, true_and, affineMin_hat hB.1 hm,
    gap_wHat hm]
  induction k using Fin.lastCases with
  | last =>
    simp [rcHat_last, Finset.mem_map, Fin.castSucc_ne_last]
  | cast k =>
    rw [rcHat_castSucc, show Fin.castSucc k = Fin.castSuccEmb k from rfl, Finset.mem_map']
    simp only [LP.improving, mem_filter, mem_univ, true_and]
    constructor
    · intro h; by_contra h'; have := not_lt.mp h'; nlinarith
    · exact mul_neg_of_pos_of_neg hκ

/-- The corral and gap correspondence needs nondegeneracy only at `B`. -/
theorem thm_a_of_nondegenerate (hm : 1 ≤ m) (hB : P.toLP.IsFeasibleBasis B)
    (hnd : P.toLP.IsNondegenerate B) :
    IsCorral P.atom (hat B) ∧
    improving P.atom (affineMin P.atom (hat B)) = (P.toLP.improving B).map Fin.castSuccEmb ∧
    ∃ κ : ℝ, 0 < κ ∧
      (∀ j : Fin n, gap P.atom (Fin.castSucc j) (affineMin P.atom (hat B)) =
        κ * P.toLP.reducedCost B j) ∧
      gap P.atom (Fin.last n) (affineMin P.atom (hat B)) = 0 := by
  refine ⟨isCorral_hat hB hnd hm, improving_hat hB hm, _, kappa_pos hB hm,
    fun j ↦ ?_, ?_⟩
  · rw [affineMin_hat hB.1 hm, gap_wHat hm, rcHat_castSucc]
  · rw [affineMin_hat hB.1 hm, gap_wHat hm, rcHat_last, mul_zero]

theorem thm_a (hP : P.IsAdmissible) (hB : P.toLP.IsFeasibleBasis B) :
    IsCorral P.atom (hat B) ∧
    improving P.atom (affineMin P.atom (hat B)) = (P.toLP.improving B).map Fin.castSuccEmb ∧
    ∃ κ : ℝ, 0 < κ ∧
      (∀ j : Fin n, gap P.atom (Fin.castSucc j) (affineMin P.atom (hat B)) =
        κ * P.toLP.reducedCost B j) ∧
      gap P.atom (Fin.last n) (affineMin P.atom (hat B)) = 0 := by
  exact thm_a_of_nondegenerate hP.1 hB (hP.2.2.2 B hB)

/-! ### Part (d) -/

lemma lamStar_nonneg (hB : P.toLP.IsFeasibleBasis B) (hnd : P.toLP.IsNondegenerate B)
    (hm : 1 ≤ m) (k : Fin (n + 1)) : 0 ≤ P.lamStar B k := by
  by_cases hk : k ∈ hat B
  · exact (P.margin_pos hm).le.trans (lamStar_ge hB hnd hm hk)
  · rw [lamStar_eq_zero hB.1 k hk]

theorem thm_d (hP : P.IsAdmissible) (hB : P.toLP.IsFeasibleBasis B) :
    (improving P.atom (affineMin P.atom (hat B)) = ∅ ∧
      IsMinNormPoint P.atom (affineMin P.atom (hat B))) ↔ P.toLP.IsOptimalBasis B := by
  have hm := hP.1
  have hnd := hP.2.2.2 B hB
  rw [LP.optimal_iff hB hnd, improving_hat hB hm, Finset.map_eq_empty]
  refine ⟨fun h ↦ h.1, fun h ↦ ⟨h, ?_⟩⟩
  rw [affineMin_hat hB.1 hm]
  apply isMinNormPoint_of_gap_nonneg
  · refine ⟨P.lamStar B, fun k _ ↦ lamStar_nonneg hB hnd hm k, sum_lamStar, ?_⟩
    exact (comb_lamStar hB.1 hm).symm
  · intro k
    rw [gap_wHat hm]
    apply mul_nonneg (kappa_pos hB hm).le
    induction k using Fin.lastCases with
    | last => simp [rcHat_last]
    | cast k =>
      rw [rcHat_castSucc]
      by_contra hlt
      have hlt := not_le.mp hlt
      have : k ∈ P.toLP.improving B := by simp [LP.improving, hlt]
      rw [h] at this
      simp at this

/-! ### Part (b): Lemma 6 (`lem:pivot`) -/

variable {j i : Fin n}

@[simp] lemma dirHat_castSucc (k : Fin n) :
    P.dirHat B j (Fin.castSucc k) = P.toLP.basicDir B j k := by
  simp [dirHat]

lemma dirHat_j (hB : P.toLP.IsBasis B) (hj : j ∉ B) : P.dirHat B j (Fin.castSucc j) = 1 := by
  rw [dirHat_castSucc]; exact (hB.basicDir_spec hj).2.1

lemma dirHat_eq_zero (hB : P.toLP.IsBasis B) (hj : j ∉ B) :
    ∀ k ∉ insert (Fin.castSucc j) (hat B), P.dirHat B j k = 0 := by
  intro k hk
  induction k using Fin.lastCases with
  | last => exact absurd (mem_insert_of_mem last_mem_hat) hk
  | cast k =>
    rw [dirHat_castSucc]
    refine (hB.basicDir_spec hj).2.2 k (fun h ↦ hk (mem_insert_of_mem (castSucc_mem_hat.2 h)))
      (fun h ↦ hk (h ▸ mem_insert_self _ _))

lemma sum_dirHat : ∑ k, P.dirHat B j k = 0 := by
  rw [dirHat, sum_snoc]; ring

lemma acomb_dirHat (hB : P.toLP.IsBasis B) (hj : j ∉ B) : P.acomb (P.dirHat B j) = 0 := by
  funext r; simp [dirHat, acomb_snoc, (hB.basicDir_spec hj).1]

lemma gcomb_dirHat (hB : P.toLP.IsBasis B) (hj : j ∉ B) :
    P.gcomb (P.dirHat B j) = P.toLP.reducedCost B j := by
  rw [dirHat, gcomb_snoc, hB.cost_basicDir hj]; ring

/-- The atoms of `B̂ ∪ {j}` are affinely independent if `c̄_j ≠ 0`. -/
lemma affIndep_insert (hB : P.toLP.IsBasis B) (hj : j ∉ B) (hrc : P.toLP.reducedCost B j ≠ 0)
    (hm : 1 ≤ m) : IsAffinelyIndependent P.atom (insert (Fin.castSucc j) (hat B)) := by
  classical
  intro β hcomb hsum l hl
  set S1 := insert (Fin.castSucc j) (hat B)
  set β' : Fin (n + 1) → ℝ := fun k ↦ if k ∈ S1 then β k else 0
  have h0 : ∀ k ∉ S1, β' k = 0 := fun k hk ↦ by simp [β', hk]
  have hc : ∑ k, β' k • P.atom k = 0 := by
    rw [← sum_eq_sum_univ_of S1 _ (fun k hk ↦ by simp [h0 k hk]), ← hcomb]
    exact Finset.sum_congr rfl fun k hk ↦ by simp [β', hk]
  have hs : ∑ k, β' k = 0 := by
    rw [← sum_eq_sum_univ_of S1 _ h0, ← hsum]
    exact Finset.sum_congr rfl fun k hk ↦ by simp [β', hk]
  rw [atom_comb] at hc
  have hN := (P.N_pos' hm).ne'
  have hac : P.acomb β' = 0 := by
    funext r
    have := congrFun hc r.succ
    simp only [Fin.cons_succ, Pi.zero_apply] at this
    simpa [hN] using this
  have hg : P.gcomb β' = 0 := by
    have := congrFun hc 0
    simp only [Fin.cons_zero, Pi.zero_apply] at this
    simpa [hN] using this
  set D := P.dirHat B j
  set β₀ := β' - β' (Fin.castSucc j) • D
  have hβ₀ : ∀ k ∉ hat B, β₀ k = 0 := by
    intro k hk
    by_cases hkj : k = Fin.castSucc j
    · subst hkj; simp [β₀, D, dirHat_j hB hj]
    · have hk1 : k ∉ S1 := by simp [S1, hkj, hk]
      simp [β₀, h0 k hk1, D, dirHat_eq_zero hB hj k hk1]
  have hac0 : P.acomb β₀ = 0 := by
    rw [acomb_sub, acomb_smul, hac, acomb_dirHat hB hj]; simp
  have hs0 : ∑ k, β₀ k = 0 := by
    simp [β₀, Finset.sum_sub_distrib, ← Finset.mul_sum, hs, D, sum_dirHat]
  have hz := eq_zero_of_acomb hB hβ₀ hac0 hs0
  have hgj : β' (Fin.castSucc j) = 0 := by
    have : P.gcomb β' = P.gcomb β₀ + β' (Fin.castSucc j) * P.gcomb D := by
      rw [← gcomb_smul, ← gcomb_add]; congr 1; simp [β₀]
    rw [hz, hg, gcomb_dirHat hB hj] at this
    have : β' (Fin.castSucc j) * P.toLP.reducedCost B j = 0 := by
      simpa [gcomb] using this.symm
    exact (mul_eq_zero.1 this).resolve_right hrc
  have : β' = 0 := by
    have : β' = β₀ + β' (Fin.castSucc j) • D := by simp [β₀]
    rw [this, hz, hgj]; simp
  have := congrFun this l
  simpa [β', hl] using this

lemma lamHat_pivot (hB : P.toLP.IsFeasibleBasis B) (hj : j ∈ P.toLP.improving B)
    (hi : P.toLP.IsLeavingLabel B j i) :
    P.lamHat (insert j (B.erase i)) =
      P.lamHat B + (P.xB B i / (-P.toLP.basicDir B j i) / P.T) • P.dirHat B j := by
  have hx' := (LP.pivot_spec hB hj hi).2
  funext k
  induction k using Fin.lastCases with
  | last =>
    simp only [lamHat, dirHat, Fin.snoc_last, Pi.add_apply, Pi.smul_apply, smul_eq_mul, xB, hx',
      Finset.sum_add_distrib, ← Finset.mul_sum]
    field_simp [P.T_pos.ne']
    ring
  | cast k =>
    simp only [lamHat, dirHat, Fin.snoc_castSucc, Pi.add_apply, Pi.smul_apply, smul_eq_mul, xB,
      hx']
    field_simp [P.T_pos.ne']

omit P in
lemma hat_pivot_eq (hiB : i ∈ B) (hjB : j ∉ B) :
    (insert (Fin.castSucc j) (hat B)).erase (Fin.castSucc i) = hat (insert j (B.erase i)) := by
  have hij : i ≠ j := fun h ↦ hjB (h ▸ hiB)
  ext k
  induction k using Fin.lastCases with
  | last =>
    have : Fin.last n ≠ Fin.castSucc i := (Fin.castSucc_ne_last i).symm
    simp [this]
  | cast k =>
    simp only [mem_erase, mem_insert, castSucc_mem_hat, Fin.castSucc_inj, ne_eq]
    constructor
    · rintro ⟨hki, hk | hk⟩
      · exact Or.inl hk
      · exact Or.inr ⟨hki, hk⟩
    · rintro (hk | ⟨hki, hk⟩)
      · exact ⟨hk ▸ hij.symm, Or.inl hk⟩
      · exact ⟨hki, Or.inr hk⟩

/-- One pivot needs nondegeneracy only at its two endpoint bases. -/
theorem thm_b_of_nondegenerate (hm : 1 ≤ m) (hB : P.toLP.IsFeasibleBasis B)
    (hj : j ∈ P.toLP.improving B) (hi : P.toLP.IsLeavingLabel B j i)
    (hnd : P.toLP.IsNondegenerate B)
    (hnd' : P.toLP.IsNondegenerate (insert j (B.erase i))) :
    ¬ IsCorral P.atom (insert (Fin.castSucc j) (hat B)) ∧
    (∃ s', MinorCycle P.atom ⟨insert (Fin.castSucc j) (hat B), affineCoeffs P.atom (hat B)⟩ s') ∧
    (∀ s', MinorCycle P.atom ⟨insert (Fin.castSucc j) (hat B), affineCoeffs P.atom (hat B)⟩ s' →
      s'.S = hat (insert j (B.erase i))) ∧
    IsCorral P.atom (hat (insert j (B.erase i))) ∧
    ∀ S' : Finset (Fin (n + 1)),
      MajorCycle P.atom (hat B) (Fin.castSucc j) S' ↔ S' = hat (insert j (B.erase i)) := by
  classical
  have hjB : j ∉ B := hB.1.not_mem_of_mem_improving hj
  have hrc : P.toLP.reducedCost B j < 0 := by simpa [LP.improving] using hj
  have hiB : i ∈ B := hi.1
  have hdi : P.toLP.basicDir B j i < 0 := hi.2.1
  obtain ⟨hB', -⟩ := LP.pivot_spec hB hj hi
  have hiB' : i ∉ insert j (B.erase i) := by
    have hij : i ≠ j := fun h ↦ hjB (h ▸ hiB)
    simp [hij]
  set B' := insert j (B.erase i) with hB'def
  set D := P.dirHat B j with hD
  set θS := P.xB B i / (-P.toLP.basicDir B j i) / P.T with hθS
  set h := P.hHat B with hh
  set τ := h / (-P.toLP.reducedCost B j) with hτ
  set μ := P.lamHat B + τ • D with hμ
  set S1 := insert (Fin.castSucc j) (hat B) with hS1
  have hlamP := lamHat_pivot hB hj hi
  rw [← hθS, ← hD] at hlamP
  have h1 : 1 ≤ h := one_le_hHat hB
  have hτpos : 0 < τ := div_pos (by linarith) (by linarith)
  have hτrc : τ * P.toLP.reducedCost B j = -h := by
    rw [hτ, div_mul_eq_mul_div, div_eq_iff (neg_ne_zero.2 hrc.ne)]; ring
  have hhP : P.hHat B' = h + θS * P.toLP.reducedCost B j := by
    rw [← gcomb_lamHat hB'.1, hlamP, gcomb_add, gcomb_smul, gcomb_lamHat hB.1, gcomb_dirHat hB.1 hjB]
  have hθτ : θS < τ := by
    have := one_le_hHat hB'
    rw [hhP] at this
    nlinarith
  -- the affine minimizer of `B̂ ∪ {j}` is the origin, with coefficients `μ`
  have hμ0 : ∀ k ∉ S1, μ k = 0 := by
    intro k hk
    have hk' : k ∉ hat B := fun h' ↦ hk (mem_insert_of_mem h')
    simp [μ, lamHat_eq_zero hB.1 k hk', D, dirHat_eq_zero hB.1 hjB k hk]
  have hμsum : ∑ k, μ k = 1 := by
    simp [μ, Finset.sum_add_distrib, ← Finset.mul_sum, sum_lamHat, D, sum_dirHat]
  have hμcomb : ∑ k, μ k • P.atom k = 0 := by
    rw [atom_comb]
    have hg : P.gcomb μ = 0 := by
      rw [hμ, gcomb_add, gcomb_smul, gcomb_lamHat hB.1, hD, gcomb_dirHat hB.1 hjB, hτrc]; ring
    have ha : P.acomb μ = 0 := by
      rw [hμ, acomb_add, acomb_smul, acomb_lamHat hB.1, hD, acomb_dirHat hB.1 hjB]; simp
    rw [hg, ha]
    funext r
    induction r using Fin.cases <;> simp
  have hindep := affIndep_insert hB.1 hjB hrc.ne hm
  have hmin1 : affineMin P.atom S1 = 0 := by
    apply affineMin_eq_of_gap_zero
    · refine ⟨μ, by rw [sum_eq_sum_univ_of _ _ hμ0, hμsum], ?_⟩
      rw [sum_eq_sum_univ_of _ _ (fun k hk ↦ by simp [hμ0 k hk]), hμcomb]
    · intro k _; simp [gap, normSq]
  have hcoef1 : affineCoeffs P.atom S1 = μ := by
    apply affineCoeffs_eq_of _ hindep hμ0
    · rw [sum_eq_sum_univ_of _ _ hμ0, hμsum]
    · rw [hmin1, sum_eq_sum_univ_of _ _ (fun k hk ↦ by simp [hμ0 k hk]), hμcomb]
  -- the coefficient of the leaving label is negative at the origin
  have hlamPi : P.lamHat B' (Fin.castSucc i) = 0 := by
    simp [lamHat, xB, hB'.1.basicSol_spec.2 i hiB']
  have hμi : μ (Fin.castSucc i) < 0 := by
    have e1 := congrFun hlamP (Fin.castSucc i)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hlamPi] at e1
    have e2 : μ (Fin.castSucc i) = (τ - θS) * D (Fin.castSucc i) := by
      simp only [μ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linarith
    rw [e2, hD, dirHat_castSucc]
    exact mul_neg_of_pos_of_neg (by linarith) hdi
  have hi'S1 : Fin.castSucc i ∈ S1 := mem_insert_of_mem (castSucc_mem_hat.2 hiB)
  have hnotc : ¬ IsCorral P.atom S1 := by
    intro hc
    have := hc.2.2 _ hi'S1
    rw [hcoef1] at this
    linarith
  -- the minor cycle
  set ls := P.lamStar B with hls
  set δ := μ - ls with hδ
  have hls_i : 0 < ls (Fin.castSucc i) :=
    lt_of_lt_of_le (P.margin_pos hm) (lamStar_ge hB hnd hm (castSucc_mem_hat.2 hiB))
  set t := ls (Fin.castSucc i) / (ls (Fin.castSucc i) - μ (Fin.castSucc i)) with ht
  have hden : 0 < ls (Fin.castSucc i) - μ (Fin.castSucc i) := by linarith
  have ht0 : 0 < t := div_pos hls_i hden
  have ht1 : t < 1 := by rw [ht, div_lt_one hden]; linarith
  have hηi : ls (Fin.castSucc i) + t * δ (Fin.castSucc i) = 0 := by
    simp only [δ, Pi.sub_apply, ht]
    field_simp
    ring
  -- the bounds of Lemma 5 (`lem:bases-corrals`)
  set ρ : ℝ := 1 / (4 * m * (P.H : ℝ) ^ 3) with hρ
  have hHp := P.H_pos
  have hεpos := eps_pos hB hm
  have hu : ∀ k, |P.eps B * P.uHat B k| ≤ ρ := fun k ↦ by
    rw [abs_mul, abs_of_pos hεpos]; exact eps_mul_abs_uHat_le hB hm k
  have hform : ∀ k, ls k + t * δ k =
      P.lamHat B' k + (t * τ - θS) * D k - (1 - t) * (P.eps B * P.uHat B k) := by
    intro k
    have e1 := congrFun hlamP k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1
    simp only [δ, ls, μ, lamStar, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [e1]; ring
  set a := t * τ - θS with ha
  have hDi := dirHat_bound hB.1 hjB (castSucc_mem_hat.2 hiB)
  have hDi_ne : D (Fin.castSucc i) ≠ 0 := by rw [hD, dirHat_castSucc]; exact hdi.ne
  have hDi_ge : 1 / (P.H : ℝ) ≤ |D (Fin.castSucc i)| := hDi.2 hDi_ne
  have haD : |a| * |D (Fin.castSucc i)| ≤ ρ := by
    have e := hform (Fin.castSucc i)
    rw [hηi, hlamPi] at e
    have : a * D (Fin.castSucc i) = (1 - t) * (P.eps B * P.uHat B (Fin.castSucc i)) := by
      linarith
    rw [← abs_mul, this, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 1 - t)]
    calc (1 - t) * |P.eps B * P.uHat B (Fin.castSucc i)| ≤ 1 * ρ :=
          mul_le_mul (by linarith) (hu _) (abs_nonneg _) zero_le_one
      _ = ρ := one_mul ρ
  have ha_le : |a| ≤ ρ * P.H := by
    have : |a| * (1 / (P.H : ℝ)) ≤ ρ :=
      le_trans (mul_le_mul_of_nonneg_left hDi_ge (abs_nonneg a)) haD
    rw [mul_one_div, div_le_iff₀ hHp] at this
    exact this
  have hρ_small : ρ * P.H * P.H + ρ < 1 / (P.H : ℝ) := by
    have hH : (1 : ℝ) ≤ P.H := by exact_mod_cast P.one_le_H
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
    rw [hρ]
    field_simp
    nlinarith [mul_le_mul_of_nonneg_left hmR (by positivity : (0 : ℝ) ≤ (P.H : ℝ) ^ 2)]
  have hpos_other : ∀ k ∈ hat B, k ≠ Fin.castSucc i → 0 < ls k + t * δ k := by
    intro k hk hki
    have hkB' : k ∈ hat B' := by
      rw [← hat_pivot_eq hiB hjB]; exact mem_erase.2 ⟨hki, mem_insert_of_mem hk⟩
    have hl := lamHat_ge hB' hnd' hkB'
    have hDk := (dirHat_bound hB.1 hjB hk).1
    have h1' : |a * D k| ≤ ρ * P.H * P.H := by
      rw [abs_mul]; exact mul_le_mul ha_le hDk (abs_nonneg _) (by positivity)
    have h2' : |(1 - t) * (P.eps B * P.uHat B k)| ≤ ρ := by
      rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 1 - t)]
      calc (1 - t) * |P.eps B * P.uHat B k| ≤ 1 * ρ :=
            mul_le_mul (by linarith) (hu _) (abs_nonneg _) zero_le_one
        _ = ρ := one_mul ρ
    rw [hform k]
    have := neg_abs_le (a * D k)
    have := le_abs_self ((1 - t) * (P.eps B * P.uHat B k))
    linarith
  have hlsj : ls (Fin.castSucc j) = 0 :=
    lamStar_eq_zero hB.1 _ (fun h' ↦ hjB (castSucc_mem_hat.1 h'))
  have hμj : μ (Fin.castSucc j) = τ := by
    simp [μ, lamHat_eq_zero hB.1 _ (fun h' ↦ hjB (castSucc_mem_hat.1 h')), D, dirHat_j hB.1 hjB]
  have hpos_j : 0 < ls (Fin.castSucc j) + t * δ (Fin.castSucc j) := by
    simp only [δ, Pi.sub_apply, hlsj, hμj, sub_zero, zero_add]
    exact mul_pos ht0 hτpos
  have hzero_out : ∀ k ∉ S1, ls k + t * δ k = 0 := by
    intro k hk
    have hk' : k ∉ hat B := fun h' ↦ hk (mem_insert_of_mem h')
    simp [δ, ls, lamStar_eq_zero hB.1 k hk', hμ0 k hk]
  have hfeas : ∀ k, 0 ≤ ls k + t * δ k := by
    intro k
    by_cases hk1 : k ∈ S1
    · rcases mem_insert.1 hk1 with hkj | hk
      · rw [hkj]; exact hpos_j.le
      · by_cases hki : k = Fin.castSucc i
        · rw [hki, hηi]
        · exact (hpos_other k hk hki).le
    · rw [hzero_out k hk1]
  have hmax : ∀ r, t < r → r ≤ 1 → ∃ k, ls k + r * δ k < 0 := by
    intro r htr _
    refine ⟨Fin.castSucc i, ?_⟩
    have hslope : δ (Fin.castSucc i) < 0 := by simp only [δ, Pi.sub_apply]; linarith
    nlinarith
  have hstep : stepLength ls δ = t := stepLength_eq ht0.le ht1.le hfeas hmax
  have hzeros : ∀ k ∈ S1, ls k + t * δ k = 0 → k = Fin.castSucc i := by
    intro k hk1 hz
    by_contra hki
    rcases mem_insert.1 hk1 with hkj | hk
    · rw [hkj] at hz; linarith
    · linarith [hpos_other k hk hki]
  have hset := hat_pivot_eq hiB hjB
  have hcorral' := isCorral_hat hB' hnd' hm
  have hcoef0 : affineCoeffs P.atom (hat B) = ls := affineCoeffs_hat hB.1 hm
  -- the minor cycles from the state after the insertion
  have hminor : ∀ s', MinorCycle P.atom ⟨S1, affineCoeffs P.atom (hat B)⟩ s' → s'.S = hat B' := by
    rintro s' ⟨-, hlam, k, hk, hk0, hS⟩
    simp only [hcoef0, hcoef1] at hlam hS hk
    rw [← hδ, hstep] at hlam
    have : ls k + t * δ k = 0 := by
      have := congrFun hlam k
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
      rw [← this]; exact hk0
    rw [hS, hzeros k hk this, hset]
  have hex : MinorCycle P.atom ⟨S1, affineCoeffs P.atom (hat B)⟩ ⟨hat B', ls + t • δ⟩ := by
    refine ⟨hnotc, ?_, Fin.castSucc i, hi'S1, ?_, ?_⟩
    · simp only [hcoef0, hcoef1]; rw [← hδ, hstep]
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; exact hηi
    · exact hset.symm
  refine ⟨hnotc, ⟨_, hex⟩, hminor, hcorral', fun S' ↦ ⟨?_, ?_⟩⟩
  · rintro ⟨-, -, lam', hrt, hc'⟩
    rcases Relation.ReflTransGen.cases_head hrt with h0 | ⟨s1, h01, h1t⟩
    · exfalso
      have : S1 = S' := congrArg State.S h0
      exact hnotc (this ▸ hc')
    · have hs1 := hminor s1 h01
      have := eq_of_reflTransGen_of_corral P.atom (hs1 ▸ hcorral') h1t
      have := congrArg State.S this
      simpa [hs1] using this
  · rintro rfl
    refine ⟨isCorral_hat hB hnd hm, ?_, ls + t • δ, Relation.ReflTransGen.single hex,
      hcorral'⟩
    rw [improving_hat hB hm]
    exact Finset.mem_map_of_mem _ hj

theorem thm_b (hP : P.IsAdmissible) (hB : P.toLP.IsFeasibleBasis B)
    (hj : j ∈ P.toLP.improving B) (hi : P.toLP.IsLeavingLabel B j i) :
    ¬ IsCorral P.atom (insert (Fin.castSucc j) (hat B)) ∧
    (∃ s', MinorCycle P.atom ⟨insert (Fin.castSucc j) (hat B), affineCoeffs P.atom (hat B)⟩ s') ∧
    (∀ s', MinorCycle P.atom ⟨insert (Fin.castSucc j) (hat B), affineCoeffs P.atom (hat B)⟩ s' →
      s'.S = hat (insert j (B.erase i))) ∧
    IsCorral P.atom (hat (insert j (B.erase i))) ∧
    ∀ S' : Finset (Fin (n + 1)),
      MajorCycle P.atom (hat B) (Fin.castSucc j) S' ↔ S' = hat (insert j (B.erase i)) := by
  exact thm_b_of_nondegenerate hP.1 hB hj hi (hP.2.2.2 B hB)
    (hP.2.2.2 _ (LP.pivot_spec hB hj hi).1)

/-! ### Part (c): runs -/

/-- The inverse of `B ↦ B̂` on sets containing the slack label. -/
def unhat (S : Finset (Fin (n + 1))) : Finset (Fin n) := univ.filter (fun k ↦ Fin.castSucc k ∈ S)

omit P in
lemma unhat_hat (B : Finset (Fin n)) : unhat (hat B) = B := by
  ext k; simp [unhat]

/-- Every major cycle at `B̂` inserts an improving label `j` of `B` and ends at the
pivot `B̂'` for a leaving label `i`. -/
lemma majorCycle_hat (hP : P.IsAdmissible) (hB : P.toLP.IsFeasibleBasis B)
    {j : Fin (n + 1)} {S' : Finset (Fin (n + 1))} (h : MajorCycle P.atom (hat B) j S') :
    ∃ j' i, j' ∈ P.toLP.improving B ∧ P.toLP.IsLeavingLabel B j' i ∧
      S' = hat (insert j' (B.erase i)) := by
  have hj := h.2.1
  rw [improving_hat hB hP.1, Finset.mem_map] at hj
  obtain ⟨j', hj', rfl⟩ := hj
  obtain ⟨i, hi⟩ := LP.exists_leavingLabel hP.2.2.1 hB hj'
  exact ⟨j', i, hj', hi, ((thm_b hP hB hj' hi).2.2.2.2 S').1 h⟩

theorem thm_c (hP : P.IsAdmissible) (B₀ : Finset (Fin n)) (hB₀ : P.toLP.IsFeasibleBasis B₀)
    (f : ℕ) (S : ℕ → Finset (Fin (n + 1))) :
    (IsWolfeRun P.atom f S ∧ S 0 = hat B₀) ↔
      ∃ B : ℕ → Finset (Fin n), P.toLP.IsSimplexRun f B ∧ B 0 = B₀ ∧
        ∀ k ≤ f, S k = hat (B k) := by
  constructor
  · rintro ⟨⟨-, hmaj, hlast⟩, hS0⟩
    set B : ℕ → Finset (Fin n) := fun k ↦ unhat (S k)
    have key : ∀ k ≤ f, P.toLP.IsFeasibleBasis (B k) ∧ S k = hat (B k) := by
      intro k
      induction k with
      | zero => intro _; simp only [B, hS0, unhat_hat]; exact ⟨hB₀, trivial⟩
      | succ k ih =>
        intro hk
        obtain ⟨hBk, hSk⟩ := ih (by omega)
        obtain ⟨j, hj⟩ := hmaj k (by omega)
        rw [hSk] at hj
        obtain ⟨j', i, hj', hi, hS'⟩ := majorCycle_hat hP hBk hj
        have hB' := (LP.pivot_spec hBk hj' hi).1
        simp only [B, hS', unhat_hat]
        exact ⟨hB', trivial⟩
    refine ⟨B, ⟨fun k hk ↦ (key k hk).1, fun k hk ↦ ?_, ?_⟩, by simp [B, hS0, unhat_hat],
      fun k hk ↦ (key k hk).2⟩
    · obtain ⟨hBk, hSk⟩ := key k hk.le
      obtain ⟨j, hj⟩ := hmaj k hk
      rw [hSk] at hj
      obtain ⟨j', i, hj', hi, hS'⟩ := majorCycle_hat hP hBk hj
      refine ⟨j', hj', hBk, hj', hBk.1.not_mem_of_mem_improving hj', i, hi, ?_⟩
      simp only [B, hS', unhat_hat]
    · obtain ⟨hBf, hSf⟩ := key f le_rfl
      rw [hSf, improving_hat hBf hP.1, Finset.map_eq_empty] at hlast
      exact hlast
  · rintro ⟨B, ⟨hfeas, hpiv, hlast⟩, hB0, hS⟩
    refine ⟨⟨fun k hk ↦ ?_, fun k hk ↦ ?_, ?_⟩, by rw [hS 0 (Nat.zero_le _), hB0]⟩
    · rw [hS k hk]; exact (thm_a hP (hfeas k hk)).1
    · obtain ⟨j, hj, -, -, -, i, hi, heq⟩ := hpiv k hk
      refine ⟨Fin.castSucc j, ?_⟩
      rw [hS k hk.le, hS (k + 1) hk, heq]
      exact ((thm_b hP (hfeas k hk.le) hj hi).2.2.2.2 _).2 rfl
    · rw [hS f le_rfl, improving_hat (hfeas f le_rfl) hP.1, hlast, Finset.map_empty]

end WolfeSimplex.IntLP
