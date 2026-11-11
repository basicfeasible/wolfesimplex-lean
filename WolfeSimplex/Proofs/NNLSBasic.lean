import WolfeSimplex.Proofs.InitRuns
import WolfeSimplex.Defs.LawsonHanson

/-!
# Nonnegative least squares: basic facts (paper: Lemma 19 (`lem:nnls-ls`))

* Affine minimizers of nonempty, affinely independent supports exist and have gap zero
  on the support (an elementary part of Lemma 1 (`lem:affine-min`)).
* Inserting an improving atom keeps affine independence (Lemma 1 (`lem:affine-min`)(b)), and the
  inserted atom gets a positive affine coefficient (the well-definedness paragraph of
  Appendix C.3 (`app:nnls`)).
* Lemma 19 (`lem:nnls-ls`).
-/

namespace WolfeSimplex

open Finset Matrix Wolfe

namespace NNLS

variable {N D : ℕ} (p : Fin N → Fin D → ℝ)

/-! ### Affine minimizers -/

lemma affIndep_subset {S T : Finset (Fin N)} (h : IsAffinelyIndependent p T) (hST : S ⊆ T) :
    IsAffinelyIndependent p S := by
  classical
  intro β h1 h2 i hi
  set β' : Fin N → ℝ := fun k ↦ if k ∈ S then β k else 0 with hβ'
  have e1 : ∑ k ∈ T, β' k • p k = ∑ k ∈ S, β k • p k := by
    rw [← Finset.sum_subset hST (fun k _ hk ↦ by simp [β', hk])]
    exact Finset.sum_congr rfl (fun k hk ↦ by simp [β', hk])
  have e2 : ∑ k ∈ T, β' k = ∑ k ∈ S, β k := by
    rw [← Finset.sum_subset hST (fun k _ hk ↦ by simp [β', hk])]
    exact Finset.sum_congr rfl (fun k hk ↦ by simp [β', hk])
  have := h β' (e1.trans h1) (e2.trans h2) i (hST hi)
  simpa [β', hi] using this

/-- Existence of affine coefficients with gap zero (the linear system of the affine
minimizer is uniquely solvable for an affinely independent support). -/
lemma exists_coeffs {S : Finset (Fin N)} (hne : S.Nonempty) (hAI : IsAffinelyIndependent p S) :
    ∃ lam : Fin N → ℝ, (∀ i ∉ S, lam i = 0) ∧ ∑ i ∈ S, lam i = 1 ∧
      ∀ i ∈ S, gap p i (∑ k ∈ S, lam k • p k) = 0 := by
  classical
  let L : ((Fin N → ℝ) × ℝ) →ₗ[ℝ] ((Fin N → ℝ) × ℝ) :=
    { toFun := fun x ↦ (fun i ↦ if i ∈ S then p i ⬝ᵥ (∑ k ∈ S, x.1 k • p k) - x.2 else x.1 i,
        ∑ k ∈ S, x.1 k)
      map_add' := by
        intro x y
        refine Prod.ext (funext fun i ↦ ?_) ?_
        · simp only [Prod.fst_add, Pi.add_apply, add_smul, Finset.sum_add_distrib,
            dotProduct_add, Prod.snd_add]
          split_ifs <;> ring
        · simp [Finset.sum_add_distrib]
      map_smul' := by
        intro r x
        refine Prod.ext (funext fun i ↦ ?_) ?_
        · simp only [Prod.smul_fst, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Prod.smul_snd,
            mul_smul, ← Finset.smul_sum, dotProduct_smul]
          split_ifs <;> ring
        · simp [Finset.mul_sum] }
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨lam, μ⟩ h
    have h1 : ∀ i, (if i ∈ S then p i ⬝ᵥ (∑ k ∈ S, lam k • p k) - μ else lam i) = 0 :=
      fun i ↦ congrFun (congrArg Prod.fst h) i
    have h2 : ∑ k ∈ S, lam k = 0 := congrArg Prod.snd h
    have hout : ∀ i ∉ S, lam i = 0 := fun i hi ↦ by simpa [hi] using h1 i
    have hin : ∀ i ∈ S, p i ⬝ᵥ (∑ k ∈ S, lam k • p k) = μ := fun i hi ↦ by
      have := h1 i; simp only [hi, ↓reduceIte] at this; linarith
    set v := ∑ k ∈ S, lam k • p k with hv
    have hvv : v ⬝ᵥ v = 0 := by
      calc v ⬝ᵥ v = ∑ k ∈ S, lam k * (p k ⬝ᵥ v) := by
              rw [hv, sum_dotProduct]; simp only [smul_dotProduct, smul_eq_mul]
        _ = ∑ k ∈ S, lam k * μ := Finset.sum_congr rfl fun k hk ↦ by rw [hin k hk]
        _ = 0 := by rw [← Finset.sum_mul, h2, zero_mul]
    have hv0 : v = 0 := dotProduct_self_eq_zero.mp hvv
    have hlam : lam = 0 := by
      funext i
      by_cases hi : i ∈ S
      · exact hAI lam hv0 h2 i hi
      · exact hout i hi
    obtain ⟨i, hi⟩ := hne
    have hμ := hin i hi
    rw [hv0, dotProduct_zero] at hμ
    rw [hlam, ← hμ]; rfl
  obtain ⟨⟨lam, μ⟩, hx⟩ := (LinearMap.injective_iff_surjective.mp hinj) ((0 : Fin N → ℝ), (1 : ℝ))
  have h1 : ∀ i, (if i ∈ S then p i ⬝ᵥ (∑ k ∈ S, lam k • p k) - μ else lam i) = 0 :=
    fun i ↦ congrFun (congrArg Prod.fst hx) i
  have h2 : ∑ k ∈ S, lam k = 1 := congrArg Prod.snd hx
  have hin : ∀ i ∈ S, p i ⬝ᵥ (∑ k ∈ S, lam k • p k) = μ := fun i hi ↦ by
    have := h1 i; simp only [hi, ↓reduceIte] at this; linarith
  refine ⟨lam, fun i hi ↦ by simpa [hi] using h1 i, h2, fun i hi ↦ ?_⟩
  have hvv : normSq (∑ k ∈ S, lam k • p k) = μ := by
    unfold normSq
    rw [sum_dotProduct]
    simp only [smul_dotProduct, smul_eq_mul]
    rw [Finset.sum_congr rfl fun k hk ↦ by rw [hin k hk], ← Finset.sum_mul, h2, one_mul]
  unfold gap
  rw [hin i hi, hvv, sub_self]

variable {p}

/-- The defining properties of `w_S` and `λ^{*S}` for a nonempty affinely independent
support: the coefficients vanish outside `S`, sum to one, combine to `w_S`, and every atom
of `S` has gap zero at `w_S`. -/
lemma coeffs_spec {S : Finset (Fin N)} (hne : S.Nonempty) (hAI : IsAffinelyIndependent p S) :
    (∀ i ∉ S, affineCoeffs p S i = 0) ∧ ∑ i ∈ S, affineCoeffs p S i = 1 ∧
      ∑ i ∈ S, affineCoeffs p S i • p i = affineMin p S ∧
      ∀ i ∈ S, gap p i (affineMin p S) = 0 := by
  obtain ⟨lam, hout, hsum, hgap⟩ := exists_coeffs p hne hAI
  have hw : affineMin p S = ∑ k ∈ S, lam k • p k :=
    affineMin_eq_of_gap_zero p ⟨lam, hsum, rfl⟩ hgap
  have hc : affineCoeffs p S = lam := affineCoeffs_eq_of p hAI hout hsum hw.symm
  rw [hc, hw]
  exact ⟨hout, hsum, rfl, hgap⟩

lemma dot_eq_normSq {S : Finset (Fin N)} (hne : S.Nonempty) (hAI : IsAffinelyIndependent p S)
    {i : Fin N} (hi : i ∈ S) : p i ⬝ᵥ affineMin p S = normSq (affineMin p S) := by
  have := (coeffs_spec hne hAI).2.2.2 i hi
  unfold gap at this; linarith

/-- `(∑_{i∈S} μ_i p_i) ᵀ w_S = (∑_{i∈S} μ_i) ‖w_S‖²`. -/
lemma comb_dot {S : Finset (Fin N)} (hne : S.Nonempty) (hAI : IsAffinelyIndependent p S)
    (mu : Fin N → ℝ) :
    (∑ i ∈ S, mu i • p i) ⬝ᵥ affineMin p S = (∑ i ∈ S, mu i) * normSq (affineMin p S) := by
  rw [sum_dotProduct, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i hi ↦ by rw [smul_dotProduct, smul_eq_mul, dot_eq_normSq hne hAI hi]

lemma corral_singleton (k : Fin N) : IsCorral p {k} := by
  have hne : ({k} : Finset (Fin N)).Nonempty := singleton_nonempty k
  have hAI : IsAffinelyIndependent p {k} := by
    intro β _ h2 i hi
    rw [mem_singleton] at hi; subst hi
    simpa using h2
  refine ⟨hne, hAI, fun i hi ↦ ?_⟩
  rw [mem_singleton] at hi; subst hi
  have := (coeffs_spec hne hAI).2.1
  rw [sum_singleton] at this
  rw [this]; exact one_pos

lemma not_mem_of_improving {S : Finset (Fin N)} (hne : S.Nonempty)
    (hAI : IsAffinelyIndependent p S) {j : Fin N} (hj : j ∈ improving p (affineMin p S)) :
    j ∉ S := by
  intro hjS
  have h1 := (coeffs_spec hne hAI).2.2.2 j hjS
  simp only [improving, mem_filter, mem_univ, true_and] at hj
  linarith

/-- Lemma 1 (`lem:affine-min`)(b), the part needed: inserting an improving atom keeps affine
independence. -/
lemma affIndep_insert {S : Finset (Fin N)} (hne : S.Nonempty) (hAI : IsAffinelyIndependent p S)
    {j : Fin N} (hj : j ∈ improving p (affineMin p S)) :
    IsAffinelyIndependent p (insert j S) := by
  have hjS := not_mem_of_improving hne hAI hj
  simp only [improving, mem_filter, mem_univ, true_and] at hj
  intro β h1 h2
  rw [sum_insert hjS] at h1 h2
  have hdot := congrArg (· ⬝ᵥ affineMin p S) h1
  simp only [add_dotProduct, smul_dotProduct, smul_eq_mul, zero_dotProduct] at hdot
  rw [comb_dot hne hAI] at hdot
  have hS : ∑ i ∈ S, β i = -β j := by linarith
  rw [hS] at hdot
  have hβj : β j * gap p j (affineMin p S) = 0 := by unfold gap; linarith
  have hβj0 : β j = 0 := (mul_eq_zero.mp hβj).resolve_right hj.ne
  rw [hβj0, zero_smul, zero_add] at h1
  rw [hβj0, zero_add] at h2
  intro i hi
  rcases mem_insert.mp hi with rfl | hi
  · exact hβj0
  · exact hAI β h1 h2 i hi

/-- The inserted improving atom gets a positive coefficient in the affine minimizer of
`S ∪ {j}` (paper: Appendix C.3 (`app:nnls`), well-definedness paragraph). -/
lemma coeff_insert_pos {S : Finset (Fin N)} (hS : IsCorral p S) {j : Fin N}
    (hj : j ∈ improving p (affineMin p S)) : 0 < affineCoeffs p (insert j S) j := by
  obtain ⟨hne, hAI, -⟩ := hS
  have hjS := not_mem_of_improving hne hAI hj
  have hAI' := affIndep_insert hne hAI hj
  have hne' : (insert j S).Nonempty := insert_nonempty j S
  obtain ⟨hout, hsum, hcomb, -⟩ := coeffs_spec hne hAI
  obtain ⟨hout', hsum', hcomb', hgap'⟩ := coeffs_spec hne' hAI'
  set w := affineMin p S
  set w' := affineMin p (insert j S)
  set l' := affineCoeffs p (insert j S)
  have hg : gap p j w < 0 := by simpa [improving] using hj
  -- `w ∈ aff(S ∪ {j})`, so `(w - w')ᵀ w' = 0`
  have hwmem : w ∈ affineHull p (insert j S) := by
    refine ⟨affineCoeffs p S, ?_, ?_⟩
    · rw [sum_insert hjS, hout j hjS, zero_add, hsum]
    · rw [sum_insert hjS, hout j hjS, zero_smul, zero_add, hcomb]
  have horth : (w - w') ⬝ᵥ w' = 0 := by
    obtain ⟨mu, hmu, hx⟩ := hwmem
    rw [hx, sub_dotProduct_eq_sum_gap p hmu]
    exact Finset.sum_eq_zero fun i hi ↦ by rw [hgap' i hi, mul_zero]
  -- `w'ᵀ w = ‖w‖² + λ'_j g_j(w)`
  have hdot : w' ⬝ᵥ w = normSq w + l' j * gap p j w := by
    rw [← hcomb', sum_insert hjS, add_dotProduct, comb_dot hne hAI, smul_dotProduct,
      smul_eq_mul]
    rw [sum_insert hjS] at hsum'
    unfold gap
    have : ∑ i ∈ S, l' i = 1 - l' j := by linarith
    rw [this]; ring
  by_contra hneg
  push Not at hneg
  have hexp := normSq_expand w w'
  rw [horth] at hexp
  have h1 : normSq w ≤ normSq w' := by
    have : w ⬝ᵥ w' = normSq w' := by
      have := horth; rw [sub_dotProduct] at this; unfold normSq; linarith
    rw [dotProduct_comm] at this
    nlinarith
  have h2 : normSq (w - w') = 0 := le_antisymm (by linarith) (normSq_nonneg _)
  have hww : w = w' := sub_eq_zero.mp (normSq_eq_zero.mp h2)
  have := hgap' j (mem_insert_self j S)
  rw [← hww] at this
  linarith

/-! ### The NNLS reduction -/

variable (p)

lemma mulVec_eq (ν : Fin N → ℝ) :
    nnlsMatrix p *ᵥ ν = Fin.snoc (α := fun _ ↦ ℝ) (∑ j, ν j • p j) (∑ j, ν j) := by
  funext r
  induction r using Fin.lastCases with
  | last =>
    simp [nnlsMatrix, mulVec, dotProduct]
  | cast r =>
    simp [nnlsMatrix, mulVec, dotProduct, Finset.sum_apply, mul_comm]

lemma resSq_eq (ν : Fin N → ℝ) :
    LH.resSq (nnlsMatrix p) (nnlsRhs D) ν = normSq (∑ j, ν j • p j) + (∑ j, ν j - 1) ^ 2 := by
  unfold LH.resSq
  rw [mulVec_eq]
  simp only [dotProduct, Fin.sum_univ_castSucc, Pi.sub_apply, nnlsRhs, Fin.snoc_castSucc,
    Fin.snoc_last, Pi.zero_apply, sub_zero, normSq]
  ring

lemma resid_eq (ν : Fin N → ℝ) (j : Fin N) :
    LH.resid (nnlsMatrix p) (nnlsRhs D) ν j = 1 - ∑ i, ν i - p j ⬝ᵥ ∑ i, ν i • p i := by
  unfold LH.resid
  rw [mulVec_eq]
  simp only [mulVec, dotProduct, Fin.sum_univ_castSucc, Pi.sub_apply, nnlsRhs, Fin.snoc_castSucc,
    Fin.snoc_last, Pi.zero_apply, zero_sub, transpose_apply, nnlsMatrix, of_apply]
  simp only [mul_neg, Finset.sum_neg_distrib, one_mul]
  ring

lemma sum_eq_of_out {S : Finset (Fin N)} {ν : Fin N → ℝ} (hout : ∀ i ∉ S, ν i = 0) :
    (∑ j, ν j • p j) = ∑ j ∈ S, ν j • p j ∧ (∑ j, ν j) = ∑ j ∈ S, ν j := by
  constructor
  · exact (Finset.sum_subset (subset_univ S) fun i _ hi ↦ by rw [hout i hi, zero_smul]).symm
  · exact (Finset.sum_subset (subset_univ S) fun i _ hi ↦ hout i hi).symm

end NNLS

/-- Lemma 19 (`lem:nnls-ls`). -/
theorem nnls_ls_main {N D : ℕ} (p : Fin N → Fin D → ℝ) (S : Finset (Fin N)) (hS : S.Nonempty)
    (hAI : IsAffinelyIndependent p S) :
    LinearIndependent ℝ (fun i : S ↦ fun r ↦ nnlsMatrix p r i) ∧
    (∀ ζ, LH.IsLsSolOf (nnlsMatrix p) (nnlsRhs D) S ζ ↔
      ζ = (1 + normSq (affineMin p S))⁻¹ • affineCoeffs p S) ∧
    ∀ j, LH.resid (nnlsMatrix p) (nnlsRhs D) ((1 + normSq (affineMin p S))⁻¹ • affineCoeffs p S) j =
      -gap p j (affineMin p S) / (1 + normSq (affineMin p S)) := by
  classical
  obtain ⟨hout, hsum, hcomb, -⟩ := NNLS.coeffs_spec hS hAI
  set w := affineMin p S
  set ρ := normSq w
  set lam := affineCoeffs p S
  have hρ : 0 ≤ ρ := normSq_nonneg w
  have h1ρ : 0 < 1 + ρ := by linarith
  set c := (1 + ρ)⁻¹ with hc
  have hc1 : c * (1 + ρ) = 1 := inv_mul_cancel₀ h1ρ.ne'
  set z := c • lam with hz
  have hzout : ∀ i ∉ S, z i = 0 := fun i hi ↦ by simp [z, hout i hi]
  have hzs : ∑ i ∈ S, z i = c := by simp [z, ← Finset.mul_sum, hsum]
  have hzc : ∑ i ∈ S, z i • p i = c • w := by
    simp [z, mul_smul, ← Finset.smul_sum, hcomb, w]
  have key : ∀ ζ, (∀ i ∉ S, ζ i = 0) → LH.resSq (nnlsMatrix p) (nnlsRhs D) ζ =
      LH.resSq (nnlsMatrix p) (nnlsRhs D) z + normSq (∑ i ∈ S, (ζ i - z i) • p i) +
        (∑ i ∈ S, (ζ i - z i)) ^ 2 := by
    intro ζ hζ
    rw [NNLS.resSq_eq, NNLS.resSq_eq, (NNLS.sum_eq_of_out p hζ).1, (NNLS.sum_eq_of_out p hζ).2,
      (NNLS.sum_eq_of_out p hzout).1, (NNLS.sum_eq_of_out p hzout).2, hzc, hzs]
    simp only [sub_smul, Finset.sum_sub_distrib, hzc, hzs]
    set u := ∑ i ∈ S, ζ i • p i
    set σ := ∑ i ∈ S, ζ i
    have hu : u ⬝ᵥ w = σ * ρ := NNLS.comb_dot hS hAI ζ
    rw [normSq_expand u (c • w)]
    have h1 : (u - c • w) ⬝ᵥ (c • w) = c * ρ * (σ - c) := by
      rw [sub_dotProduct, dotProduct_smul, smul_dotProduct, hu, smul_eq_mul, smul_eq_mul]
      simp only [ρ, normSq, dotProduct_smul, smul_eq_mul]; ring
    rw [h1]
    linear_combination (2 * (σ - c)) * hc1
  refine ⟨?_, fun ζ ↦ ⟨fun ⟨hζout, hmin⟩ ↦ ?_, ?_⟩, fun j ↦ ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    set β : Fin N → ℝ := fun i ↦ if h : i ∈ S then g ⟨i, h⟩ else 0
    have e : ∀ F : Fin N → ℝ, ∑ i : S, g i * F i = ∑ i ∈ S, β i * F i := by
      intro F
      rw [← Finset.sum_coe_sort S]
      exact Finset.sum_congr rfl fun i _ ↦ by simp [β, i.2]
    have hrow : ∀ r, ∑ i : S, g i * nnlsMatrix p r i = 0 := fun r ↦ by
      have := congrFun hg r
      simpa [Finset.sum_apply] using this
    have hA : ∑ i ∈ S, β i • p i = 0 := by
      funext k
      have := hrow (Fin.castSucc k)
      rw [e] at this
      simpa [nnlsMatrix, Finset.sum_apply] using this
    have hB : ∑ i ∈ S, β i = 0 := by
      have := hrow (Fin.last D)
      rw [e] at this
      simpa [nnlsMatrix] using this
    intro i
    have := hAI β hA hB i i.2
    simpa [β, i.2] using this
  · have hle := hmin z hzout
    rw [key ζ hζout] at hle
    have hA := normSq_nonneg (∑ i ∈ S, (ζ i - z i) • p i)
    have hB := sq_nonneg (∑ i ∈ S, (ζ i - z i))
    have hA0 : normSq (∑ i ∈ S, (ζ i - z i) • p i) = 0 := by linarith
    have hB0 : (∑ i ∈ S, (ζ i - z i)) ^ 2 = 0 := by linarith
    have h0 := hAI (ζ - z) (by simpa using normSq_eq_zero.mp hA0) (by simpa using hB0)
    funext i
    by_cases hi : i ∈ S
    · exact sub_eq_zero.mp (h0 i hi)
    · rw [hζout i hi, hzout i hi]
  · rintro rfl
    refine ⟨hzout, fun ζ' h' ↦ ?_⟩
    rw [key ζ' h']
    have hA := normSq_nonneg (∑ i ∈ S, (ζ' i - z i) • p i)
    have hB := sq_nonneg (∑ i ∈ S, (ζ' i - z i))
    linarith
  · rw [NNLS.resid_eq, (NNLS.sum_eq_of_out p hzout).1, (NNLS.sum_eq_of_out p hzout).2, hzc, hzs,
      dotProduct_smul, smul_eq_mul]
    unfold gap
    rw [div_eq_mul_inv, ← hc]
    linear_combination (-1) * hc1

namespace NNLS

variable {N D : ℕ} {p : Fin N → Fin D → ℝ}

lemma lsSol_eq {S : Finset (Fin N)} (hS : S.Nonempty) (hAI : IsAffinelyIndependent p S) :
    LH.lsSol (nnlsMatrix p) (nnlsRhs D) S = (1 + normSq (affineMin p S))⁻¹ • affineCoeffs p S := by
  have h := (nnls_ls_main p S hS hAI).2.1
  exact (h _).1 (Classical.epsilon_spec ⟨_, (h _).2 rfl⟩)

lemma c_pos (S : Finset (Fin N)) : 0 < (1 + normSq (affineMin p S))⁻¹ :=
  inv_pos.2 (by linarith [normSq_nonneg (affineMin p S)])

lemma resid_lsSol {S : Finset (Fin N)} (hS : S.Nonempty) (hAI : IsAffinelyIndependent p S)
    (j : Fin N) :
    LH.resid (nnlsMatrix p) (nnlsRhs D) (LH.lsSol (nnlsMatrix p) (nnlsRhs D) S) j =
      -gap p j (affineMin p S) * (1 + normSq (affineMin p S))⁻¹ := by
  rw [lsSol_eq hS hAI, (nnls_ls_main p S hS hAI).2.2 j, div_eq_mul_inv]

/-! ### One inner iteration is one minor cycle -/

/-- The invariant of the Wolfe states reached by minor cycles inside a major cycle. -/
structure WInv (p : Fin N → Fin D → ℝ) (w : Wolfe.State N) : Prop where
  ne : w.S.Nonempty
  ai : IsAffinelyIndependent p w.S
  out : ∀ k ∉ w.S, w.lam k = 0
  nonneg : ∀ k, 0 ≤ w.lam k
  pos : ∀ i ∈ w.S, affineCoeffs p w.S i ≤ 0 → 0 < w.lam i

/-- Every minor cycle from `w` sets only one coefficient (of `w.S`) to zero. -/
def SZ (p : Fin N → Fin D → ℝ) (w : Wolfe.State N) : Prop :=
  ∀ s', MinorCycle p w s' → ∀ i ∈ w.S, ∀ i' ∈ w.S, s'.lam i = 0 → s'.lam i' = 0 → i = i'

variable {w : Wolfe.State N}

lemma erase_nonempty_of_not_corral {S : Finset (Fin N)} (hne : S.Nonempty)
    (hnc : ¬ IsCorral p S) (i : Fin N) : (S.erase i).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro h
  rcases (Finset.erase_eq_empty_iff S i).1 h with h | h
  · exact hne.ne_empty h
  · exact hnc (h ▸ corral_singleton i)

/-- The computation behind Lemma 20 (`lem:lh-wolfe`): at a Wolfe state `(S, λ)` with the
invariant, the Lawson–Hanson inner iteration from `ν = cλ` has a unique step length `ϑ`,
and the new vector is a positive multiple of Wolfe's new coefficients `λ + t d`; the
label `i0` attaining the minimum gets coefficient zero. -/
lemma step_calc (hw : WInv p w) (hnc : ¬ IsCorral p w.S) {c : ℝ} (hc : 0 < c) :
    ∃ i0 ∈ w.S, ∃ ϑ C : ℝ, 0 < C ∧
      (∀ ϑ', LH.IsInnerStep w.S (c • w.lam)
          ((1 + normSq (affineMin p w.S))⁻¹ • affineCoeffs p w.S) ϑ' ↔ ϑ' = ϑ) ∧
      (∀ k, (c • w.lam) k + ϑ * (((1 + normSq (affineMin p w.S))⁻¹ • affineCoeffs p w.S) k -
          (c • w.lam) k) =
        C * (w.lam + stepLength w.lam (affineCoeffs p w.S - w.lam) •
          (affineCoeffs p w.S - w.lam)) k) ∧
      (w.lam + stepLength w.lam (affineCoeffs p w.S - w.lam) •
          (affineCoeffs p w.S - w.lam)) i0 = 0 ∧
      (∀ k, 0 ≤ (w.lam + stepLength w.lam (affineCoeffs p w.S - w.lam) •
          (affineCoeffs p w.S - w.lam)) k) ∧
      affineCoeffs p w.S i0 ≤ 0 := by
  classical
  obtain ⟨hout, -, -, -⟩ := coeffs_spec hw.ne hw.ai
  have hc' : 0 < (1 + normSq (affineMin p w.S))⁻¹ := c_pos w.S
  set L := affineCoeffs p w.S with hL
  set c' := (1 + normSq (affineMin p w.S))⁻¹ with hc'def
  set lam := w.lam with hlam
  set Neg := w.S.filter (fun i ↦ L i ≤ 0) with hNegdef
  have hNeg : Neg.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at h
    exact hnc ⟨hw.ne, hw.ai, fun i hi ↦ lt_of_not_ge (h hi)⟩
  set r : Fin N → ℝ := fun i ↦ (c * lam i) / (c * lam i - c' * L i) with hr
  obtain ⟨i0, hi0, hmin⟩ := Neg.exists_min_image r hNeg
  rw [mem_filter] at hi0
  have hNegpos : ∀ i ∈ w.S, L i ≤ 0 →
      0 < c * lam i ∧ 0 < c * lam i - c' * L i ∧ 0 < r i ∧ r i ≤ 1 := by
    intro i hi hLi
    have h1 : 0 < c * lam i := mul_pos hc (hw.pos i hi hLi)
    have h2 : c' * L i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc'.le hLi
    have h3 : 0 < c * lam i - c' * L i := by linarith
    exact ⟨h1, h3, div_pos h1 h3, (div_le_one h3).2 (by linarith)⟩
  have hrzero : ∀ i ∈ w.S, L i ≤ 0 → c * lam i + r i * (c' * L i - c * lam i) = 0 := by
    intro i hi hLi
    have := (hNegpos i hi hLi).2.1
    simp only [r]
    field_simp
    ring
  set ϑ := r i0 with hϑdef
  obtain ⟨-, -, hϑ0, hϑ1⟩ := hNegpos i0 hi0.1 hi0.2
  have hϑmin : ∀ i ∈ w.S, L i ≤ 0 → ϑ ≤ r i := fun i hi hLi ↦ hmin i (mem_filter.2 ⟨hi, hLi⟩)
  set C := (1 - ϑ) * c + ϑ * c' with hCdef
  have hC : 0 < C := add_pos_of_nonneg_of_pos (mul_nonneg (by linarith) hc.le) (mul_pos hϑ0 hc')
  set τ := ϑ * c' / C with hτdef
  have hτ0 : 0 ≤ τ := div_nonneg (mul_nonneg hϑ0.le hc'.le) hC.le
  have hτ1 : τ ≤ 1 := by
    rw [div_le_one hC]
    nlinarith [mul_nonneg (sub_nonneg.2 hϑ1) hc.le]
  have hid : ∀ k, c * lam k + ϑ * (c' * L k - c * lam k) = C * (lam k + τ * (L k - lam k)) := by
    intro k
    simp only [hτdef]
    field_simp
    ring
  have hnew_nonneg : ∀ k, 0 ≤ c * lam k + ϑ * (c' * L k - c * lam k) := by
    intro k
    by_cases hk : k ∈ w.S
    · by_cases hLk : L k ≤ 0
      · obtain ⟨ha, hb, -, -⟩ := hNegpos k hk hLk
        have h1 := hϑmin k hk hLk
        have h2 := hrzero k hk hLk
        nlinarith
      · push Not at hLk
        have := hw.nonneg k
        nlinarith [mul_nonneg (sub_nonneg.2 hϑ1) (mul_nonneg hc.le this),
          mul_pos hϑ0 (mul_pos hc' hLk)]
    · have h1 : lam k = 0 := hw.out k hk
      rw [h1, hout k hk]; simp
  have hfeas : ∀ k, 0 ≤ lam k + τ * (L k - lam k) := fun k ↦ by
    have := hnew_nonneg k
    rw [hid k] at this
    exact (mul_nonneg_iff_of_pos_left hC).1 this
  have hzero : lam i0 + τ * (L i0 - lam i0) = 0 := by
    have h1 := hrzero i0 hi0.1 hi0.2
    rw [← hϑdef, hid] at h1
    exact (mul_eq_zero.1 h1).resolve_left hC.ne'
  have hstep : stepLength lam (L - lam) = τ := by
    apply stepLength_eq hτ0 hτ1
    · intro k; simpa using hfeas k
    · intro r' hr' _
      refine ⟨i0, ?_⟩
      have hd : L i0 - lam i0 < 0 := by
        have := hw.pos i0 hi0.1 hi0.2; linarith [hi0.2]
      simp only [Pi.sub_apply]
      nlinarith [hzero]
  refine ⟨i0, hi0.1, ϑ, C, hC, ?_, ?_, ?_, ?_, hi0.2⟩
  · intro ϑ'
    simp only [LH.IsInnerStep, Pi.smul_apply, smul_eq_mul]
    constructor
    · rintro ⟨⟨i, hi, hζ, rfl⟩, hall⟩
      have hLi : L i ≤ 0 := by
        by_contra h; push Not at h; nlinarith [mul_pos hc' h]
      exact le_antisymm (hall i0 hi0.1 (mul_nonpos_of_nonneg_of_nonpos hc'.le hi0.2))
        (hϑmin i hi hLi)
    · rintro rfl
      refine ⟨⟨i0, hi0.1, mul_nonpos_of_nonneg_of_nonpos hc'.le hi0.2, rfl⟩, fun i hi hζ ↦ ?_⟩
      have hLi : L i ≤ 0 := by
        by_contra h; push Not at h; nlinarith [mul_pos hc' h]
      exact hϑmin i hi hLi
  · intro k
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hstep]
    exact hid k
  · simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hstep]
    exact hzero
  · intro k
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hstep]
    exact hfeas k

lemma not_corral_of_lsSol (hne : w.S.Nonempty) (hai : IsAffinelyIndependent p w.S)
    {i : Fin N} (hi : i ∈ w.S) (h : LH.lsSol (nnlsMatrix p) (nnlsRhs D) w.S i ≤ 0) :
    ¬ IsCorral p w.S := by
  rintro ⟨-, -, hpos⟩
  rw [lsSol_eq hne hai, Pi.smul_apply, smul_eq_mul] at h
  nlinarith [mul_pos (c_pos (p := p) w.S) (hpos i hi)]

/-- An inner iteration from `(S, cλ)` is a minor cycle from `(S, λ)`. -/
lemma inner_fwd (hw : WInv p w) (hsz : SZ p w) {c : ℝ} (hc : 0 < c) {s' : LH.State N}
    (h : LH.InnerStep (nnlsMatrix p) (nnlsRhs D) ⟨.inner, w.S, c • w.lam⟩ s') :
    ∃ w', MinorCycle p w w' ∧ ∃ c' : ℝ, 0 < c' ∧ s' = ⟨.inner, w'.S, c' • w'.lam⟩ := by
  obtain ⟨-, ⟨i, hi, hζ⟩, ϑ', hϑ', rfl⟩ := h
  have hnc := not_corral_of_lsSol hw.ne hw.ai hi hζ
  rw [lsSol_eq hw.ne hw.ai] at hϑ' ⊢
  obtain ⟨i0, hi0, ϑ, C, hC, hiff, hid, hz, -, -⟩ := step_calc hw hnc hc
  obtain rfl := (hiff ϑ').1 hϑ'
  set lam' := w.lam + stepLength w.lam (affineCoeffs p w.S - w.lam) • (affineCoeffs p w.S - w.lam)
  let w' : Wolfe.State N := ⟨w.S.erase i0, lam'⟩
  have hmc : MinorCycle p w w' := ⟨hnc, rfl, i0, hi0, hz, rfl⟩
  refine ⟨w', hmc, C, hC, ?_⟩
  have hzeros : ∀ i ∈ w.S, lam' i = 0 → i = i0 := fun i hi h ↦ hsz w' hmc i hi i0 hi0 h hz
  simp only [LH.State.mk.injEq, true_and]
  constructor
  · ext i
    simp only [w', mem_filter, mem_erase, hid, ne_eq, mul_eq_zero, hC.ne', false_or]
    have h1 := hzeros i
    have h2 : i = i0 → lam' i = 0 := fun h ↦ h ▸ hz
    tauto
  · funext k
    have := hid k
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at this ⊢
    rw [this]

/-- A minor cycle from `(S, λ)` is an inner iteration from `(S, cλ)`. -/
lemma inner_bwd (hw : WInv p w) (hsz : SZ p w) {c : ℝ} (hc : 0 < c) {w' : Wolfe.State N}
    (hmc : MinorCycle p w w') :
    ∃ c' : ℝ, 0 < c' ∧ LH.InnerStep (nnlsMatrix p) (nnlsRhs D) ⟨.inner, w.S, c • w.lam⟩
      ⟨.inner, w'.S, c' • w'.lam⟩ := by
  obtain ⟨hnc, hlam, i, hi, hzi, hS'⟩ := hmc
  obtain ⟨i0, hi0, ϑ, C, hC, hiff, hid, hz, -, hL0⟩ := step_calc hw hnc hc
  have hii0 : i = i0 :=
    hsz w' ⟨hnc, hlam, i, hi, hzi, hS'⟩ i hi i0 hi0 hzi (by rw [hlam]; exact hz)
  subst hii0
  refine ⟨C, hC, rfl, ⟨i, hi, ?_⟩, ϑ, ?_, ?_⟩
  · rw [lsSol_eq hw.ne hw.ai, Pi.smul_apply, smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos (c_pos w.S).le hL0
  · rw [lsSol_eq hw.ne hw.ai]; exact (hiff ϑ).2 rfl
  · simp only [LH.State.mk.injEq, true_and]
    rw [lsSol_eq hw.ne hw.ai, hS', hlam]
    have hzeros : ∀ k ∈ w.S, w'.lam k = 0 → k = i := fun k hk h ↦
      hsz w' ⟨hnc, hlam, i, hi, hzi, hS'⟩ k hk i hi h hzi
    rw [hlam] at hzeros
    constructor
    · ext k
      simp only [mem_filter, mem_erase, hid, ne_eq, mul_eq_zero, hC.ne', false_or]
      have h1 := hzeros k
      have h2 : k = i → (w.lam + stepLength w.lam (affineCoeffs p w.S - w.lam) •
          (affineCoeffs p w.S - w.lam)) k = 0 := fun h ↦ h ▸ hz
      tauto
    · funext k
      have := hid k
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at this ⊢
      rw [this]

/-- The invariant is kept by minor cycles. -/
lemma minor_inv (hw : WInv p w) (hsz : SZ p w) {w' : Wolfe.State N} (hmc : MinorCycle p w w') :
    WInv p w' := by
  obtain ⟨hnc, hlam, i, hi, hzi, hS'⟩ := hmc
  obtain ⟨-, -, -, -, -, -, -, -, hnn, -⟩ := step_calc hw hnc one_pos
  obtain ⟨hout, -, -, -⟩ := coeffs_spec hw.ne hw.ai
  have hzeros : ∀ k ∈ w.S, w'.lam k = 0 → k = i := fun k hk h ↦
    hsz w' ⟨hnc, hlam, i, hi, hzi, hS'⟩ k hk i hi h hzi
  have hnn' : ∀ k, 0 ≤ w'.lam k := by rw [hlam]; exact hnn
  refine ⟨?_, ?_, fun k hk ↦ ?_, hnn', fun k hk _ ↦ ?_⟩
  · rw [hS']; exact erase_nonempty_of_not_corral hw.ne hnc i
  · rw [hS']; exact affIndep_subset p hw.ai (erase_subset i w.S)
  · rw [hS', mem_erase, not_and_or, not_not] at hk
    rcases hk with rfl | hk
    · exact hzi
    · rw [hlam]; simp [hw.out k hk, hout k hk]
  · rw [hS', mem_erase] at hk
    exact lt_of_le_of_ne (hnn' k) (fun h ↦ hk.1 (hzeros k hk.2 h.symm))

lemma accept_iff {F : Finset (Fin N)} (hne : F.Nonempty) (hai : IsAffinelyIndependent p F)
    (ν : Fin N → ℝ) (s' : LH.State N) :
    LH.AcceptStep (nnlsMatrix p) (nnlsRhs D) ⟨.inner, F, ν⟩ s' ↔
      IsCorral p F ∧ s' = ⟨.outer, F, LH.lsSol (nnlsMatrix p) (nnlsRhs D) F⟩ := by
  simp only [LH.AcceptStep, true_and]
  have hc := c_pos (p := p) F
  have : (∀ i ∈ F, 0 < LH.lsSol (nnlsMatrix p) (nnlsRhs D) F i) ↔ IsCorral p F := by
    rw [lsSol_eq hne hai]
    simp only [Pi.smul_apply, smul_eq_mul]
    constructor
    · intro h; exact ⟨hne, hai, fun i hi ↦ pos_of_mul_pos_right (h i hi) hc.le⟩
    · rintro ⟨-, -, h⟩ i hi; exact mul_pos hc (h i hi)
  rw [this]

lemma no_inner_of_corral {F : Finset (Fin N)} (hF : IsCorral p F) (ν : Fin N → ℝ)
    (s' : LH.State N) : ¬ LH.InnerStep (nnlsMatrix p) (nnlsRhs D) ⟨.inner, F, ν⟩ s' := by
  rintro ⟨-, ⟨i, hi, h⟩, -⟩
  exact not_corral_of_lsSol (w := ⟨F, 0⟩) hF.1 hF.2.1 hi h hF

/-- The start of a major cycle satisfies the invariant. -/
lemma winv_start {S : Finset (Fin N)} (hS : IsCorral p S) {j : Fin N}
    (hj : j ∈ improving p (affineMin p S)) : WInv p ⟨insert j S, affineCoeffs p S⟩ := by
  obtain ⟨hne, hai, hpos⟩ := hS
  obtain ⟨hout, -, -, -⟩ := coeffs_spec hne hai
  refine ⟨insert_nonempty j S, affIndep_insert hne hai hj, fun k hk ↦ hout k (fun h ↦ hk
    (mem_insert_of_mem h)), fun k ↦ ?_, fun i hi hL ↦ ?_⟩
  · by_cases hk : k ∈ S
    · exact (hpos k hk).le
    · exact (hout k hk).ge
  · rcases mem_insert.1 hi with rfl | hi
    · exact absurd hL (not_le.2 (coeff_insert_pos ⟨hne, hai, hpos⟩ hj))
    · exact hpos i hi

end NNLS

end WolfeSimplex
