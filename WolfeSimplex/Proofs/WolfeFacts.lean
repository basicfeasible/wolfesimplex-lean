import WolfeSimplex.Defs.Wolfe

/-!
# General facts about Wolfe's method

Parts of Lemma 1 (`lem:affine-min`) (Wolfe's criteria) and small facts about the
step length and the minor cycles.
-/

namespace WolfeSimplex.Wolfe

open Finset Matrix

variable {n D : ℕ} (p : Fin n → Fin D → ℝ)

/-- `‖v‖² ≥ 0`. -/
theorem normSq_nonneg (v : Fin D → ℝ) : 0 ≤ normSq v := by
  unfold normSq dotProduct
  exact Finset.sum_nonneg fun i _ ↦ mul_self_nonneg (v i)

/-- `‖v‖² = 0` iff `v = 0`. -/
theorem normSq_eq_zero {v : Fin D → ℝ} : normSq v = 0 ↔ v = 0 :=
  dotProduct_self_eq_zero

/-- `‖x‖² = ‖w‖² + 2 (x - w)ᵀw + ‖x - w‖²`. -/
theorem normSq_expand (x w : Fin D → ℝ) :
    normSq x = normSq w + 2 * ((x - w) ⬝ᵥ w) + normSq (x - w) := by
  unfold normSq
  simp only [sub_dotProduct, dotProduct_sub, dotProduct_comm w x]
  ring

/-- For `x = ∑_{i∈S} μ_i p_i` with `∑_{i∈S} μ_i = 1`:
`(x - w)ᵀw = ∑_{i∈S} μ_i g_i(w)`. -/
theorem sub_dotProduct_eq_sum_gap {S : Finset (Fin n)} {mu : Fin n → ℝ}
    (hsum : ∑ i ∈ S, mu i = 1) (w : Fin D → ℝ) :
    (∑ i ∈ S, mu i • p i - w) ⬝ᵥ w = ∑ i ∈ S, mu i * gap p i w := by
  rw [sub_dotProduct, sum_dotProduct]
  simp only [smul_dotProduct, smul_eq_mul, gap, mul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_mul, hsum, one_mul, normSq]

/-- Lemma 1 (`lem:affine-min`)(a), the direction needed: if `w ∈ aff(S)` and every
atom of `S` has gap zero at `w`, then `w` is the affine minimizer of `S`. -/
theorem affineMin_eq_of_gap_zero {S : Finset (Fin n)} {w : Fin D → ℝ}
    (hw : w ∈ affineHull p S) (hgap : ∀ i ∈ S, gap p i w = 0) :
    affineMin p S = w := by
  -- every `x ∈ aff(S)` satisfies `(x - w)ᵀw = 0`
  have horth : ∀ x ∈ affineHull p S, (x - w) ⬝ᵥ w = 0 := by
    rintro x ⟨mu, hmu, rfl⟩
    rw [sub_dotProduct_eq_sum_gap p hmu]
    exact Finset.sum_eq_zero fun i hi ↦ by rw [hgap i hi, mul_zero]
  have hmin : IsAffineMinimizerOf p S w := by
    refine ⟨hw, fun x hx ↦ ?_⟩
    rw [normSq_expand x w, horth x hx]
    linarith [normSq_nonneg (x - w)]
  have hspec : IsAffineMinimizerOf p S (affineMin p S) :=
    Classical.epsilon_spec (p := IsAffineMinimizerOf p S) ⟨w, hmin⟩
  set w' := affineMin p S
  have h1 : normSq w' ≤ normSq w := hspec.2 w hw
  have h2 := normSq_expand w' w
  rw [horth w' hspec.1] at h2
  have h3 : normSq (w' - w) = 0 :=
    le_antisymm (by linarith) (normSq_nonneg _)
  exact sub_eq_zero.mp (normSq_eq_zero.mp h3)

/-- Uniqueness of affine coefficients for an affinely independent support. -/
theorem affineCoeffs_eq_of {S : Finset (Fin n)} (hS : IsAffinelyIndependent p S)
    {lam : Fin n → ℝ} (hout : ∀ i ∉ S, lam i = 0) (hsum : ∑ i ∈ S, lam i = 1)
    (hcomb : ∑ i ∈ S, lam i • p i = affineMin p S) :
    affineCoeffs p S = lam := by
  have hspec : IsAffineCoeffsOf p S (affineCoeffs p S) :=
    Classical.epsilon_spec (p := IsAffineCoeffsOf p S) ⟨lam, hout, hsum, hcomb⟩
  obtain ⟨hout', hsum', hcomb'⟩ := hspec
  have h0 := hS (affineCoeffs p S - lam)
    (by simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, hcomb, hcomb', sub_self])
    (by simp only [Pi.sub_apply, Finset.sum_sub_distrib, hsum, hsum', sub_self])
  funext i
  by_cases hi : i ∈ S
  · exact sub_eq_zero.mp (h0 i hi)
  · rw [hout i hi, hout' i hi]

/-- Lemma 1 (`lem:affine-min`)(c), the direction needed: a point of the convex hull
of all atoms at which no atom has negative gap is the minimum-norm point. -/
theorem isMinNormPoint_of_gap_nonneg {w : Fin D → ℝ} (hw : w ∈ convexHull p univ)
    (hgap : ∀ j, 0 ≤ gap p j w) : IsMinNormPoint p w := by
  refine ⟨hw, ?_⟩
  rintro x ⟨mu, hmu0, hmu, rfl⟩
  have h : 0 ≤ (∑ i ∈ univ, mu i • p i - w) ⬝ᵥ w := by
    rw [sub_dotProduct_eq_sum_gap p hmu]
    exact Finset.sum_nonneg fun i hi ↦ mul_nonneg (hmu0 i hi) (hgap i)
  rw [normSq_expand (∑ i ∈ univ, mu i • p i) w]
  linarith [normSq_nonneg (∑ i ∈ univ, mu i • p i - w)]

/-- Computing the step length: if `t ∈ [0,1]` is feasible and every larger
`r ∈ (t,1]` is infeasible, then `stepLength lam d = t`. -/
theorem stepLength_eq {lam d : Fin n → ℝ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hfeas : ∀ k, 0 ≤ lam k + t * d k)
    (hmax : ∀ r, t < r → r ≤ 1 → ∃ k, lam k + r * d k < 0) :
    stepLength lam d = t := by
  unfold stepLength
  refine IsGreatest.csSup_eq ⟨⟨ht0, ht1, hfeas⟩, ?_⟩
  rintro r ⟨-, hr1, hr⟩
  by_contra hlt
  obtain ⟨k, hk⟩ := hmax r (lt_of_not_ge hlt) hr1
  exact absurd (hr k) (not_le.mpr hk)

/-- No minor cycle starts at a corral, so a sequence of minor cycles that starts
at a corral is empty. -/
theorem eq_of_reflTransGen_of_corral {s t : State n} (hs : IsCorral p s.S)
    (h : Relation.ReflTransGen (MinorCycle p) s t) : t = s := by
  rcases h.cases_head with h | ⟨c, hc, -⟩
  · exact h.symm
  · exact absurd hs hc.1

end WolfeSimplex.Wolfe
