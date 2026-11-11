import WolfeSimplex.Defs.Cap
import WolfeSimplex.Defs.RandomRules
import WolfeSimplex.Proofs.RuleRuns
import WolfeSimplex.Proofs.InducedLemmasTBound
import WolfeSimplex.Proofs.Shield

/-!
# Facts about the capped LP (paper: Appendix C.2 (`app:cor-rules`) (cap argument))

Notation: `L = P.toLP` (the original LP), `Q = P.cap.toLP` (the capped LP), `M = capBound`.

* The entries of `Q`, and the maps `capPr z = (z_k)_{k ∈ [n]}` and
  `capLift t x = (x, t - 1ᵀx)`, which identify the solutions of `Q.A z = Q.b` with the
  solutions `x` of `L.A x = L.b` (via `z = capLift (M+1) (capPr z)`).
* `sum_basicSol_le`: `1ᵀx^B ≤ M` for every basis `B` of `L` (Cramer's rule).
* Feasible points of `L` (under rank `m` and nondegeneracy): support reduction, existence
  of a feasible basis, and: a feasible point with at most `m` nonzero coordinates is a basic
  solution (`exists_basis_of_card_support_le`).
* `B ↦ B̂`: bases, basic solutions, basic directions, reduced costs, improving sets, leaving
  labels, pivots.
-/

namespace WolfeSimplex

open Finset Matrix

variable {m n : ℕ}

/-! ### The maps `capPr` and `capLift` -/

/-- `capPr z = (z_k)_{k ∈ [n]}`: forget the cap coordinate. -/
def capPr (z : Fin (n + 1) → ℝ) : Fin n → ℝ := fun k ↦ z k.castSucc

/-- `capLift t x = (x, t - 1ᵀx)`. -/
noncomputable def capLift (t : ℝ) (x : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.snoc (α := fun _ ↦ ℝ) x (t - ∑ k, x k)

@[simp] lemma capLift_castSucc (t : ℝ) (x : Fin n → ℝ) (k : Fin n) :
    capLift t x k.castSucc = x k := by
  simp [capLift]

@[simp] lemma capLift_last (t : ℝ) (x : Fin n → ℝ) :
    capLift t x (Fin.last n) = t - ∑ k, x k := by
  simp [capLift]

@[simp] lemma capPr_apply (z : Fin (n + 1) → ℝ) (k : Fin n) : capPr z k = z k.castSucc := rfl

@[simp] lemma capPr_capLift (t : ℝ) (x : Fin n → ℝ) : capPr (capLift t x) = x := by
  funext k; simp

lemma sum_capLift (t : ℝ) (x : Fin n → ℝ) : ∑ ℓ, capLift t x ℓ = t := by
  rw [Fin.sum_univ_castSucc]; simp

lemma eq_capLift (z : Fin (n + 1) → ℝ) : z = capLift (∑ ℓ, z ℓ) (capPr z) := by
  funext ℓ
  induction ℓ using Fin.lastCases with
  | last => rw [capLift_last, Fin.sum_univ_castSucc]; simp
  | cast k => simp

lemma capLift_add_smul (t t' r : ℝ) (x x' : Fin n → ℝ) :
    capLift t x + r • capLift t' x' = capLift (t + r * t') (x + r • x') := by
  funext ℓ
  induction ℓ using Fin.lastCases with
  | last =>
    simp only [Pi.add_apply, Pi.smul_apply, capLift_last, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    ring
  | cast k => simp

lemma capLift_eq_zero_of_not_mem_hat {B : Finset (Fin n)} {x : Fin n → ℝ} (t : ℝ)
    (hx : ∀ k ∉ B, x k = 0) : ∀ ℓ ∉ hat B, capLift t x ℓ = 0 := by
  intro ℓ hℓ
  induction ℓ using Fin.lastCases with
  | last => exact absurd IntLP.last_mem_hat hℓ
  | cast k => simpa using hx k (by simpa using hℓ)

namespace IntLP

variable (P : IntLP m n)

/-! ### The entries of the capped LP -/

@[simp] lemma capZ_A_cc (i : Fin m) (k : Fin n) : P.cap.A i.castSucc k.castSucc = P.A i k := by
  simp [cap]

@[simp] lemma capZ_A_cl (i : Fin m) : P.cap.A i.castSucc (Fin.last n) = 0 := by
  simp [cap]

@[simp] lemma capZ_A_l (ℓ : Fin (n + 1)) : P.cap.A (Fin.last m) ℓ = 1 := by
  simp [cap]

@[simp] lemma capZ_b_c (i : Fin m) : P.cap.b i.castSucc = P.b i := by
  simp [cap]

@[simp] lemma capZ_b_l : P.cap.b (Fin.last m) = (P.capBound : ℤ) + 1 := by
  simp [cap]

@[simp] lemma capZ_c_c (k : Fin n) : P.cap.c k.castSucc = P.c k := by
  simp [cap]

@[simp] lemma capZ_c_l : P.cap.c (Fin.last n) = 0 := by
  simp [cap]

lemma cap_A_cc (i : Fin m) (k : Fin n) :
    P.cap.toLP.A i.castSucc k.castSucc = (P.A i k : ℝ) := by
  simp [cap]

lemma cap_A_cl (i : Fin m) : P.cap.toLP.A i.castSucc (Fin.last n) = 0 := by
  simp [cap]

lemma cap_A_l (ℓ : Fin (n + 1)) : P.cap.toLP.A (Fin.last m) ℓ = 1 := by
  simp [cap]

lemma cap_b_c (i : Fin m) : P.cap.toLP.b i.castSucc = (P.b i : ℝ) := by
  simp [cap, toLP]

lemma cap_b_l : P.cap.toLP.b (Fin.last m) = (P.capBound : ℝ) + 1 := by
  simp [cap, toLP]

lemma cap_c_c (k : Fin n) : P.cap.toLP.c k.castSucc = (P.c k : ℝ) := by
  simp [cap, toLP]

lemma cap_c_l : P.cap.toLP.c (Fin.last n) = 0 := by
  simp [cap, toLP]

lemma cap_mulVec_castSucc (z : Fin (n + 1) → ℝ) (i : Fin m) :
    (P.cap.toLP.A *ᵥ z) i.castSucc = (P.toLP.A *ᵥ capPr z) i := by
  simp [mulVec, dotProduct, Fin.sum_univ_castSucc]

lemma cap_mulVec_last (z : Fin (n + 1) → ℝ) :
    (P.cap.toLP.A *ᵥ z) (Fin.last m) = ∑ ℓ, z ℓ := by
  simp [mulVec, dotProduct]

lemma cap_mulVec_eq_b_iff (z : Fin (n + 1) → ℝ) :
    P.cap.toLP.A *ᵥ z = P.cap.toLP.b ↔
      P.toLP.A *ᵥ capPr z = P.toLP.b ∧ ∑ ℓ, z ℓ = (P.capBound : ℝ) + 1 := by
  rw [funext_iff, Fin.forall_fin_succ', funext_iff]
  simp [cap_mulVec_castSucc, cap_mulVec_last]

lemma cap_mulVec_eq_zero_iff (z : Fin (n + 1) → ℝ) :
    P.cap.toLP.A *ᵥ z = 0 ↔ P.toLP.A *ᵥ capPr z = 0 ∧ ∑ ℓ, z ℓ = 0 := by
  rw [funext_iff, Fin.forall_fin_succ', funext_iff]
  simp only [cap_mulVec_castSucc, cap_mulVec_last, Pi.zero_apply]

lemma cap_mulVec_capLift_eq_b_iff (x : Fin n → ℝ) :
    P.cap.toLP.A *ᵥ capLift ((P.capBound : ℝ) + 1) x = P.cap.toLP.b ↔
      P.toLP.A *ᵥ x = P.toLP.b := by
  rw [cap_mulVec_eq_b_iff, capPr_capLift, sum_capLift]; simp

end IntLP

/-! ### Feasible points of an LP: support reduction -/

namespace LP

variable (P : LP m n)

/-- If the columns of the support of a feasible point `x` are linearly dependent, there is a
feasible point whose support is strictly smaller. -/
theorem exists_feasible_support_ssubset {x : Fin n → ℝ} (hx : P.IsFeasible x)
    (hdep : ¬ LinearIndependent ℝ
      (fun j : (univ.filter fun j ↦ x j ≠ 0) ↦ P.col (j : Fin n))) :
    ∃ x', P.IsFeasible x' ∧
      univ.filter (fun j ↦ x' j ≠ 0) ⊂ univ.filter (fun j ↦ x j ≠ 0) := by
  classical
  set S := univ.filter (fun j ↦ x j ≠ 0) with hS
  have hoff : ∀ j ∉ S, x j = 0 := fun j hj ↦ by simpa [hS] using hj
  have hz' : ∃ z : Fin n → ℝ, (∀ j ∉ S, z j = 0) ∧ P.A *ᵥ z = 0 ∧ z ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hdep ((linIndep_iff P S).2 fun z h1 h2 ↦ by
      by_contra h3; exact h3 (hcon z h1 h2))
  obtain ⟨z₀, hz₀off, hAz₀, hz₀ne⟩ := hz'
  -- choose the sign such that `z` has a negative entry
  obtain ⟨z, hzoff, hAz, hzneg⟩ : ∃ z : Fin n → ℝ, (∀ j ∉ S, z j = 0) ∧
      P.A *ᵥ z = 0 ∧ ∃ j, z j < 0 := by
    by_cases hneg : ∃ j, z₀ j < 0
    · exact ⟨z₀, hz₀off, hAz₀, hneg⟩
    · push Not at hneg
      obtain ⟨j, hj⟩ := Function.ne_iff.1 hz₀ne
      have hpos : 0 < z₀ j := lt_of_le_of_ne (hneg j) (Ne.symm hj)
      refine ⟨-z₀, fun k hk ↦ by simp [hz₀off k hk],
        by rw [Matrix.mulVec_neg, hAz₀, neg_zero],
        j, by simp [hpos]⟩
  set N := univ.filter (fun j ↦ z j < 0) with hN
  have hNne : N.Nonempty := by
    obtain ⟨j, hj⟩ := hzneg
    exact ⟨j, by simp [hN, hj]⟩
  have hxpos : ∀ j ∈ N, 0 < x j := by
    intro j hj
    have hzj : z j < 0 := by simpa [hN] using hj
    have hjS : j ∈ S := by
      by_contra hjS
      rw [hzoff j hjS] at hzj
      exact lt_irrefl _ hzj
    have hxj : x j ≠ 0 := by simpa [hS] using hjS
    exact lt_of_le_of_ne (hx.2 j) (Ne.symm hxj)
  set t := N.inf' hNne (fun j ↦ x j / (-z j)) with ht
  obtain ⟨k₀, hk₀N, hk₀⟩ := Finset.exists_mem_eq_inf' hNne (fun j ↦ x j / (-z j))
  have hzk₀ : z k₀ < 0 := by simpa [hN] using hk₀N
  have ht0 : 0 ≤ t := by
    rw [ht, hk₀]
    exact div_nonneg (hxpos k₀ hk₀N).le (by linarith)
  set x' := x + t • z with hx'
  have hx'feas : P.IsFeasible x' := by
    refine ⟨?_, fun j ↦ ?_⟩
    · rw [hx', Matrix.mulVec_add, Matrix.mulVec_smul, hAz, smul_zero, add_zero, hx.1]
    · simp only [hx', Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      by_cases hzj : z j < 0
      · have hjN : j ∈ N := by simp [hN, hzj]
        have hle : t ≤ x j / (-z j) := Finset.inf'_le _ hjN
        rw [le_div_iff₀ (by linarith)] at hle
        linarith
      · push Not at hzj
        exact add_nonneg (hx.2 j) (mul_nonneg ht0 hzj)
  have hx'k₀ : x' k₀ = 0 := by
    simp only [hx', Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [ht, hk₀]
    have hz0 : z k₀ ≠ 0 := hzk₀.ne
    field_simp
    ring
  refine ⟨x', hx'feas, ?_⟩
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨k₀, ?_, ?_⟩
    · have := hxpos k₀ hk₀N
      simp [hS, this.ne']
    · simp [hx'k₀]
  · intro j hj
    have hj' : x' j ≠ 0 := by simpa using hj
    by_contra hjS
    apply hj'
    simp [hx', hoff j hjS, hzoff j hjS]

/-- A feasible point gives a feasible basis (when `rank A = m`). -/
theorem exists_feasibleBasis (hrank : P.A.rank = m) {x : Fin n → ℝ} (hx : P.IsFeasible x) :
    ∃ B, P.IsFeasibleBasis B := by
  classical
  induction hk : (univ.filter (fun j ↦ x j ≠ 0)).card using Nat.strong_induction_on
    generalizing x with
  | _ k ih =>
  set S := univ.filter (fun j ↦ x j ≠ 0) with hS
  have hoff : ∀ j ∉ S, x j = 0 := fun j hj ↦ by simpa [hS] using hj
  by_cases hind : LinearIndependent ℝ (fun j : S ↦ P.col (j : Fin n))
  · obtain ⟨B, hSB, hB⟩ := P.exists_basis_superset hrank S hind
    have hxB : x = P.basicSol B := hB.eq_basicSol hx.1 (fun j hj ↦ hoff j (fun h ↦ hj (hSB h)))
    exact ⟨B, hB, fun j ↦ hxB ▸ hx.2 j⟩
  · obtain ⟨x', hx', hsub⟩ := P.exists_feasible_support_ssubset hx hind
    exact ih _ (hk ▸ Finset.card_lt_card hsub) hx' rfl

/-- Under rank `m` and nondegeneracy, every feasible point has at least `m` nonzero
coordinates. -/
theorem card_support_ge (hrank : P.A.rank = m)
    (hnd : ∀ B, P.IsFeasibleBasis B → P.IsNondegenerate B) {x : Fin n → ℝ}
    (hx : P.IsFeasible x) : m ≤ (univ.filter (fun j ↦ x j ≠ 0)).card := by
  classical
  induction hk : (univ.filter (fun j ↦ x j ≠ 0)).card using Nat.strong_induction_on
    generalizing x with
  | _ k ih =>
  set S := univ.filter (fun j ↦ x j ≠ 0) with hS
  have hoff : ∀ j ∉ S, x j = 0 := fun j hj ↦ by simpa [hS] using hj
  by_cases hind : LinearIndependent ℝ (fun j : S ↦ P.col (j : Fin n))
  · obtain ⟨B, hSB, hB⟩ := P.exists_basis_superset hrank S hind
    have hxB : x = P.basicSol B := hB.eq_basicSol hx.1 (fun j hj ↦ hoff j (fun h ↦ hj (hSB h)))
    have hBf : P.IsFeasibleBasis B := ⟨hB, fun j ↦ hxB ▸ hx.2 j⟩
    have hBS : B ⊆ S := by
      intro i hi
      have := hnd B hBf i hi
      rw [← hxB] at this
      simp [hS, this.ne']
    rw [← hk, ← hB.1]
    exact Finset.card_le_card hBS
  · obtain ⟨x', hx', hsub⟩ := P.exists_feasible_support_ssubset hx hind
    have hlt := hk ▸ Finset.card_lt_card hsub
    have := ih _ hlt hx' rfl
    omega

/-- Under rank `m` and nondegeneracy, a feasible point with at most `m` nonzero coordinates is
the basic solution of a basis. -/
theorem exists_basis_of_card_support_le (hrank : P.A.rank = m)
    (hnd : ∀ B, P.IsFeasibleBasis B → P.IsNondegenerate B) {x : Fin n → ℝ}
    (hx : P.IsFeasible x) (hcard : (univ.filter (fun j ↦ x j ≠ 0)).card ≤ m) :
    ∃ B, P.IsBasis B ∧ x = P.basicSol B := by
  classical
  set S := univ.filter (fun j ↦ x j ≠ 0) with hS
  have hoff : ∀ j ∉ S, x j = 0 := fun j hj ↦ by simpa [hS] using hj
  by_cases hind : LinearIndependent ℝ (fun j : S ↦ P.col (j : Fin n))
  · obtain ⟨B, hSB, hB⟩ := P.exists_basis_superset hrank S hind
    exact ⟨B, hB, hB.eq_basicSol hx.1 (fun j hj ↦ hoff j (fun h ↦ hj (hSB h)))⟩
  · exfalso
    obtain ⟨x', hx', hsub⟩ := P.exists_feasible_support_ssubset hx hind
    have h1 : (univ.filter fun j ↦ x' j ≠ 0).card < S.card := Finset.card_lt_card hsub
    have h2 := P.card_support_ge hrank hnd hx'
    omega

/-- If the optimum is finite, the pivot on an improving label has a leaving label. -/
theorem exists_leavingLabel_of_opt (hopt : ∃ x, P.IsOptimalSolution x) {B : Finset (Fin n)}
    (hB : P.IsFeasibleBasis B) {j : Fin n} (hj : j ∈ P.improving B) :
    ∃ i, P.IsLeavingLabel B j i := by
  have hjB := hB.1.not_mem_of_mem_improving hj
  have hrc : P.reducedCost B j < 0 := by simpa [improving] using hj
  set x := P.basicSol B
  set d := P.basicDir B j
  set S := B.filter (fun k ↦ d k < 0) with hS
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · exfalso
    obtain ⟨xs, hxs, hxsopt⟩ := hopt
    have hd : ∀ k, 0 ≤ d k := by
      intro k
      by_cases hk : k ∈ B
      · by_contra hneg
        have : k ∈ S := by simp [hS, hk, not_le.1 hneg]
        rw [hSe] at this
        exact absurd this (Finset.notMem_empty k)
      · exact hB.1.basicDir_nonneg_of_not_mem hjB hk
    have hfeas : ∀ r : ℝ, 0 ≤ r → P.IsFeasible (x + r • d) := fun r hr ↦
      ⟨hB.1.mulVec_add_smul_basicDir hjB r,
        fun k ↦ by simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
                   exact add_nonneg (hB.2 k) (mul_nonneg hr (hd k))⟩
    have hx : P.IsFeasible x := ⟨hB.1.basicSol_spec.1, hB.2⟩
    have h0 := hxsopt x hx
    set r := (P.c ⬝ᵥ x - P.c ⬝ᵥ xs + 1) / (-P.reducedCost B j) with hr
    have hr0 : 0 ≤ r := div_nonneg (by linarith) (by linarith)
    have h1 := hxsopt _ (hfeas r hr0)
    rw [dotProduct_add, dotProduct_smul, hB.1.cost_basicDir hjB, smul_eq_mul] at h1
    have h2 : r * P.reducedCost B j = -(P.c ⬝ᵥ x - P.c ⬝ᵥ xs + 1) := by
      have hne : P.reducedCost B j ≠ 0 := hrc.ne
      rw [hr]; field_simp
    linarith
  · obtain ⟨i, hiS, hmin⟩ := Finset.exists_min_image S (fun k ↦ x k / (-d k)) hSne
    simp only [hS, Finset.mem_filter] at hiS hmin
    exact ⟨i, hiS.1, hiS.2, fun k hk hdk ↦ hmin k ⟨hk, hdk⟩⟩

/-- In a nondegenerate LP, the leaving label is unique. -/
theorem isLeavingLabel_unique (hnd : ∀ B, P.IsFeasibleBasis B → P.IsNondegenerate B)
    {B : Finset (Fin n)} (hB : P.IsFeasibleBasis B) {j : Fin n} (hj : j ∈ P.improving B)
    {i i' : Fin n} (hi : P.IsLeavingLabel B j i) (hi' : P.IsLeavingLabel B j i') : i = i' := by
  by_contra hne
  obtain ⟨hfeas, heq⟩ := P.pivot_spec hB hj hi
  have hmem : i' ∈ insert j (B.erase i) :=
    Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨Ne.symm hne, hi'.1⟩)
  have hpos := hnd _ hfeas i' hmem
  rw [heq] at hpos
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hpos
  have h1 := hi.2.2 i' hi'.1 hi'.2.1
  have h2 := hi'.2.2 i hi.1 hi.2.1
  have hθ : P.basicSol B i / -P.basicDir B j i = P.basicSol B i' / -P.basicDir B j i' :=
    le_antisymm h1 h2
  rw [hθ] at hpos
  have hd : P.basicDir B j i' ≠ 0 := hi'.2.1.ne
  have : P.basicSol B i' + P.basicSol B i' / -P.basicDir B j i' * P.basicDir B j i' = 0 := by
    field_simp; ring
  linarith

end LP

/-! ### `B ↦ B̂` for the capped LP -/

namespace IntLP

variable (P : IntLP m n)

/-- `1ᵀx^B ≤ M` for every basis `B` (Cramer's rule, `|x^B_k| ≤ m! U^m ≤ (mU)^m`). -/
lemma sum_basicSol_le {B : Finset (Fin n)} (hB : P.toLP.IsBasis B) :
    ∑ k, P.toLP.basicSol B k ≤ (P.capBound : ℝ) := by
  have hs : ∑ k, P.toLP.basicSol B k = ∑ k ∈ B, P.toLP.basicSol B k :=
    (Finset.sum_subset (subset_univ B)
      (fun k _ hk ↦ by simp [hB.basicSol_spec.2 k hk])).symm
  have hle : ∑ k ∈ B, P.toLP.basicSol B k ≤ m * ((m.factorial * P.U ^ m : ℕ) : ℝ) := by
    calc ∑ k ∈ B, P.toLP.basicSol B k ≤ ∑ k ∈ B, ((m.factorial * P.U ^ m : ℕ) : ℝ) :=
          Finset.sum_le_sum fun k _ ↦ (le_abs_self _).trans (P.abs_xB_le hB k)
      _ = m * ((m.factorial * P.U ^ m : ℕ) : ℝ) := by simp [hB.1]
  have hnat : m * (m.factorial * P.U ^ m) ≤ P.capBound := by
    unfold capBound
    rw [mul_pow]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.factorial_le_pow _))
  have hreal : (m : ℝ) * ((m.factorial * P.U ^ m : ℕ) : ℝ) ≤ (P.capBound : ℝ) := by
    exact_mod_cast hnat
  rw [hs]; linarith

lemma isBasis_hat_cap {B : Finset (Fin n)} (hB : P.toLP.IsBasis B) :
    P.cap.toLP.IsBasis (hat B) := by
  refine ⟨by rw [card_hat, hB.1], ?_⟩
  rw [LP.linIndep_iff]
  intro z hz hAz
  rw [cap_mulVec_eq_zero_iff] at hAz
  have hpr : capPr z = 0 := hB.eq_zero (fun k hk ↦ by
    simpa using hz k.castSucc (by simpa using hk)) hAz.1
  rw [eq_capLift z, hpr, hAz.2]
  funext ℓ
  induction ℓ using Fin.lastCases with
  | last => simp
  | cast k => simp

lemma isBasis_of_hat_cap {B : Finset (Fin n)} (hB : P.cap.toLP.IsBasis (hat B)) :
    P.toLP.IsBasis B := by
  refine ⟨by have := hB.1; rw [card_hat] at this; omega, ?_⟩
  rw [LP.linIndep_iff]
  intro x hx hAx
  have h0 := hB.eq_zero (capLift_eq_zero_of_not_mem_hat 0 hx)
    (by rw [cap_mulVec_eq_zero_iff, capPr_capLift, sum_capLift]; exact ⟨hAx, rfl⟩)
  rw [← capPr_capLift 0 x, h0]; rfl

lemma basicSol_hat_cap {B : Finset (Fin n)} (hB : P.toLP.IsBasis B) :
    P.cap.toLP.basicSol (hat B) = capLift ((P.capBound : ℝ) + 1) (P.toLP.basicSol B) :=
  ((P.isBasis_hat_cap hB).eq_basicSol ((P.cap_mulVec_capLift_eq_b_iff _).2 hB.basicSol_spec.1)
    (capLift_eq_zero_of_not_mem_hat _ hB.basicSol_spec.2)).symm

lemma one_le_basicSol_hat_cap_last {B : Finset (Fin n)} (hB : P.toLP.IsBasis B) :
    1 ≤ P.cap.toLP.basicSol (hat B) (Fin.last n) := by
  rw [P.basicSol_hat_cap hB, capLift_last]
  linarith [P.sum_basicSol_le hB]

lemma isFeasibleBasis_hat_cap {B : Finset (Fin n)} (hB : P.toLP.IsFeasibleBasis B) :
    P.cap.toLP.IsFeasibleBasis (hat B) := by
  refine ⟨P.isBasis_hat_cap hB.1, fun ℓ ↦ ?_⟩
  induction ℓ using Fin.lastCases with
  | last => linarith [P.one_le_basicSol_hat_cap_last hB.1]
  | cast k => rw [P.basicSol_hat_cap hB.1, capLift_castSucc]; exact hB.2 k

lemma basicDir_hat_cap {B : Finset (Fin n)} (hB : P.toLP.IsBasis B) {j : Fin n} (hj : j ∉ B) :
    P.cap.toLP.basicDir (hat B) j.castSucc = capLift 0 (P.toLP.basicDir B j) := by
  obtain ⟨h1, h2, h3⟩ := hB.basicDir_spec hj
  refine ((P.isBasis_hat_cap hB).eq_basicDir (by simpa using hj) ⟨?_, ?_, ?_⟩).symm
  · rw [cap_mulVec_eq_zero_iff, capPr_capLift, sum_capLift]; exact ⟨h1, rfl⟩
  · simp [h2]
  · intro ℓ hℓ hℓj
    induction ℓ using Fin.lastCases with
    | last => exact absurd last_mem_hat hℓ
    | cast k => simp [h3 k (by simpa using hℓ) (fun e ↦ hℓj (by rw [e]))]

lemma reducedCost_hat_cap {B : Finset (Fin n)} (hB : P.toLP.IsBasis B) (j : Fin n) :
    P.cap.toLP.reducedCost (hat B) j.castSucc = P.toLP.reducedCost B j := by
  by_cases hj : j ∈ B
  · rw [hB.reducedCost_of_mem hj, (P.isBasis_hat_cap hB).reducedCost_of_mem (by simpa using hj)]
  · rw [← hB.cost_basicDir hj, ← (P.isBasis_hat_cap hB).cost_basicDir (by simpa using hj),
      P.basicDir_hat_cap hB hj]
    simp [dotProduct, Fin.sum_univ_castSucc]

lemma improving_hat_cap {B : Finset (Fin n)} (hB : P.toLP.IsBasis B) :
    P.cap.toLP.improving (hat B) = (P.toLP.improving B).map Fin.castSuccEmb := by
  ext ℓ
  induction ℓ using Fin.lastCases with
  | last =>
    simp only [LP.improving, mem_filter, mem_univ, true_and, mem_map, Fin.castSuccEmb_apply,
      Fin.castSucc_ne_last, and_false, exists_false, iff_false, not_lt]
    rw [(P.isBasis_hat_cap hB).reducedCost_of_mem last_mem_hat]
  | cast k =>
    simp only [LP.improving, mem_filter, mem_univ, true_and, mem_map, Fin.castSuccEmb_apply,
      Fin.castSucc_inj, exists_eq_right]
    rw [P.reducedCost_hat_cap hB]

/-- Leaving labels correspond (the cap never leaves). -/
lemma isLeavingLabel_hat_cap_iff (hopt : ∃ x, P.toLP.IsOptimalSolution x)
    {B : Finset (Fin n)} (hB : P.toLP.IsFeasibleBasis B) {j : Fin n}
    (hj : j ∈ P.toLP.improving B) (i' : Fin (n + 1)) :
    P.cap.toLP.IsLeavingLabel (hat B) j.castSucc i' ↔
      ∃ i, i' = i.castSucc ∧ P.toLP.IsLeavingLabel B j i := by
  have hjB := hB.1.not_mem_of_mem_improving hj
  have hx' := P.basicSol_hat_cap hB.1
  have hd' := P.basicDir_hat_cap hB.1 hjB
  set x := P.toLP.basicSol B
  set d := P.toLP.basicDir B j
  have hdc : ∀ k, P.cap.toLP.basicDir (hat B) j.castSucc k.castSucc = d k := by
    intro k; rw [hd', capLift_castSucc]
  have hxc : ∀ k, P.cap.toLP.basicSol (hat B) k.castSucc = x k := by
    intro k; rw [hx', capLift_castSucc]
  have key : ∀ i₀, P.toLP.IsLeavingLabel B j i₀ →
      P.cap.toLP.basicDir (hat B) j.castSucc (Fin.last n) < 0 →
      x i₀ / (-d i₀) < P.cap.toLP.basicSol (hat B) (Fin.last n) /
        (-P.cap.toLP.basicDir (hat B) j.castSucc (Fin.last n)) := by
    intro i₀ hi₀ hω
    obtain ⟨hfeas, heq⟩ := P.toLP.pivot_spec hB hj hi₀
    set θ := x i₀ / (-d i₀)
    have hz : P.cap.toLP.basicSol (hat B) + θ • P.cap.toLP.basicDir (hat B) j.castSucc =
        capLift ((P.capBound : ℝ) + 1) (P.toLP.basicSol (insert j (B.erase i₀))) := by
      rw [hx', hd', capLift_add_smul, mul_zero, add_zero, heq]
    have hpos := congrFun hz (Fin.last n)
    rw [capLift_last] at hpos
    have hsum := P.sum_basicSol_le hfeas.1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hpos
    rw [lt_div_iff₀ (by linarith)]
    linarith
  constructor
  · rintro ⟨hi'B, hi'd, hmin⟩
    obtain ⟨i₀, hi₀⟩ := P.toLP.exists_leavingLabel_of_opt hopt hB hj
    induction i' using Fin.lastCases with
    | last =>
      exfalso
      have h1 := key i₀ hi₀ hi'd
      have h2 := hmin i₀.castSucc (by simpa using hi₀.1) (by rw [hdc]; exact hi₀.2.1)
      rw [hxc, hdc] at h2
      linarith
    | cast i =>
      rw [hdc] at hi'd
      refine ⟨i, rfl, by simpa using hi'B, hi'd, fun k hk hdk ↦ ?_⟩
      have h2 := hmin k.castSucc (by simpa using hk) (by rw [hdc]; exact hdk)
      rwa [hxc, hdc, hxc, hdc] at h2
  · rintro ⟨i, rfl, hi⟩
    refine ⟨by simpa using hi.1, by rw [hdc]; exact hi.2.1, fun k' hk' hdk' ↦ ?_⟩
    rw [hxc, hdc]
    induction k' using Fin.lastCases with
    | last => exact (key i hi hdk').le
    | cast k =>
      rw [hdc] at hdk'
      rw [hxc, hdc]
      exact hi.2.2 k (by simpa using hk') hdk'

/-- Pivots at `B̂` are the hats of the pivots at `B`. -/
lemma isPivot_hat_cap_iff (hopt : ∃ x, P.toLP.IsOptimalSolution x)
    {B : Finset (Fin n)} (hB : P.toLP.IsFeasibleBasis B) (j' : Fin (n + 1))
    (S' : Finset (Fin (n + 1))) :
    P.cap.toLP.IsPivot (hat B) j' S' ↔
      ∃ j B', j' = Fin.castSucc j ∧ P.toLP.IsPivot B j B' ∧ S' = hat B' := by
  constructor
  · rintro ⟨-, hj', -, i', hi', heq⟩
    rw [P.improving_hat_cap hB.1] at hj'
    obtain ⟨j, hj, hjj⟩ := Finset.mem_map.1 hj'
    obtain rfl : Fin.castSucc j = j' := hjj
    obtain ⟨i, rfl, hi⟩ := (P.isLeavingLabel_hat_cap_iff hopt hB hj i').1 hi'
    exact ⟨j, insert j (B.erase i), rfl,
      ⟨hB, hj, hB.1.not_mem_of_mem_improving hj, i, hi, rfl⟩,
      by rw [heq, hat_insert_erase]⟩
  · rintro ⟨j, B', rfl, ⟨-, hj, hjB, i, hi, rfl⟩, rfl⟩
    refine ⟨P.isFeasibleBasis_hat_cap hB, ?_, by simpa using hjB, i.castSucc,
      (P.isLeavingLabel_hat_cap_iff hopt hB hj _).2 ⟨i, rfl, hi⟩,
      (hat_insert_erase B j i).symm⟩
    rw [P.improving_hat_cap hB.1]; exact Finset.mem_map_of_mem _ hj

/-! ### Admissibility of the capped LP -/

omit P in
lemma hat_unhat_of_last_mem {B' : Finset (Fin (n + 1))} (h : Fin.last n ∈ B') :
    hat (unhat B') = B' := by
  ext ℓ
  induction ℓ using Fin.lastCases with
  | last => simp [h, last_mem_hat]
  | cast k => simp [unhat]

omit P in
lemma unhat_map_of_last_not_mem {B' : Finset (Fin (n + 1))} (h : Fin.last n ∉ B') :
    (unhat B').map Fin.castSuccEmb = B' := by
  ext ℓ
  induction ℓ using Fin.lastCases with
  | last => simp [h, Fin.castSucc_ne_last]
  | cast k => simp [unhat]

lemma cap_abs_le {z : Fin (n + 1) → ℝ} (hz : P.cap.toLP.IsFeasible z) (ℓ : Fin (n + 1)) :
    |z ℓ| ≤ (P.capBound : ℝ) + 1 := by
  rw [abs_of_nonneg (hz.2 ℓ)]
  have hs := ((P.cap_mulVec_eq_b_iff z).1 hz.1).2
  rw [← hs]
  exact Finset.single_le_sum (f := z) (fun k _ ↦ hz.2 k) (mem_univ ℓ)

lemma cap_rank {B : Finset (Fin n)} (hB : P.toLP.IsBasis B) : P.cap.toLP.A.rank = m + 1 := by
  have hB' := P.isBasis_hat_cap hB
  have hsurj : LinearMap.range P.cap.toLP.A.mulVecLin = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro r
    obtain ⟨x, hx, -⟩ := hB'.exists_sol r
    exact ⟨x, by simpa using hx⟩
  rw [Matrix.rank, hsurj, finrank_top, Module.finrank_fin_fun]

/-- Every feasible basis of the capped LP is nondegenerate. -/
lemma cap_nondegenerate (hrank : P.toLP.A.rank = m)
    (hnd : ∀ B, P.toLP.IsFeasibleBasis B → P.toLP.IsNondegenerate B) :
    ∀ B', P.cap.toLP.IsFeasibleBasis B' → P.cap.toLP.IsNondegenerate B' := by
  intro B' hB'
  by_cases hlast : Fin.last n ∈ B'
  · obtain ⟨B, rfl⟩ : ∃ B, B' = hat B := ⟨unhat B', (hat_unhat_of_last_mem hlast).symm⟩
    have hBb := P.isBasis_of_hat_cap hB'.1
    have hBf : P.toLP.IsFeasibleBasis B := ⟨hBb, fun k ↦ by
      have := hB'.2 k.castSucc; rwa [P.basicSol_hat_cap hBb, capLift_castSucc] at this⟩
    intro ℓ hℓ
    induction ℓ using Fin.lastCases with
    | last => linarith [P.one_le_basicSol_hat_cap_last hBb]
    | cast k =>
      rw [P.basicSol_hat_cap hBb, capLift_castSucc]
      exact hnd B hBf k (by simpa using hℓ)
  · intro ℓ hℓ
    by_contra hle
    push Not at hle
    set z := P.cap.toLP.basicSol B'
    have hzℓ : z ℓ = 0 := le_antisymm hle (hB'.2 ℓ)
    obtain ⟨hAz, hz0⟩ := hB'.1.basicSol_spec
    rw [cap_mulVec_eq_b_iff] at hAz
    have hzl : z (Fin.last n) = 0 := hz0 _ hlast
    set x := capPr z with hxdef
    have hxf : P.toLP.IsFeasible x := ⟨hAz.1, fun k ↦ hB'.2 _⟩
    have hsum : ∑ k, x k = (P.capBound : ℝ) + 1 := by
      have := hAz.2
      have hzl' : P.cap.toLP.basicSol B' (Fin.last n) = 0 := hzl
      rw [Fin.sum_univ_castSucc, hzl', add_zero] at this
      exact this
    obtain ⟨i, rfl⟩ : ∃ i, ℓ = Fin.castSucc i := by
      induction ℓ using Fin.lastCases with
      | last => exact absurd hℓ hlast
      | cast i => exact ⟨i, rfl⟩
    have hsupp : univ.filter (fun k ↦ x k ≠ 0) ⊆ (unhat B').erase i := by
      intro k hk
      have hk' : z k.castSucc ≠ 0 := by simpa [hxdef] using hk
      refine Finset.mem_erase.2 ⟨fun e ↦ hk' (e ▸ hzℓ), ?_⟩
      simp only [unhat, mem_filter, mem_univ, true_and]
      by_contra hkB; exact hk' (hz0 _ hkB)
    have hcard : (univ.filter (fun k ↦ x k ≠ 0)).card ≤ m := by
      have h1 := Finset.card_le_card hsupp
      have h2 : (unhat B').card = m + 1 := by
        have := congrArg Finset.card (unhat_map_of_last_not_mem hlast)
        rw [card_map] at this
        rw [this, hB'.1.1]
      have hi : i ∈ unhat B' := by simpa [unhat] using hℓ
      rw [Finset.card_erase_of_mem hi, h2] at h1
      omega
    obtain ⟨B, hB, hxB⟩ := P.toLP.exists_basis_of_card_support_le hrank hnd hxf hcard
    have := P.sum_basicSol_le hB
    rw [← hxB] at this
    linarith

/-- The capped LP is admissible. -/
theorem cap_isAdmissible (hrank : P.toLP.A.rank = m)
    (hopt : ∃ x, P.toLP.IsOptimalSolution x)
    (hnd : ∀ B, P.toLP.IsFeasibleBasis B → P.toLP.IsNondegenerate B) :
    P.cap.IsAdmissible := by
  obtain ⟨x, hx⟩ := hopt
  obtain ⟨B, hB⟩ := P.toLP.exists_feasibleBasis hrank hx.1
  have hQ := P.isFeasibleBasis_hat_cap hB
  exact ⟨by omega, P.cap_rank hB.1,
    ⟨⟨_, hQ.1.basicSol_spec.1, hQ.2⟩, (P.capBound : ℝ) + 1,
      fun z hz ℓ ↦ P.cap_abs_le hz ℓ⟩,
    P.cap_nondegenerate hrank hnd⟩

/-! ### Unique pivots -/

/-- With a finite optimum and nondegeneracy, the pivot on an improving label is unique. -/
lemma isPivot_iff_eq_pivotTo (hopt : ∃ x, P.toLP.IsOptimalSolution x)
    (hnd : ∀ B, P.toLP.IsFeasibleBasis B → P.toLP.IsNondegenerate B)
    {B : Finset (Fin n)} (hB : P.toLP.IsFeasibleBasis B) {j : Fin n}
    (hj : j ∈ P.toLP.improving B) :
    ∀ B', P.toLP.IsPivot B j B' ↔ B' = P.toLP.pivotTo B j := by
  obtain ⟨i, hi⟩ := P.toLP.exists_leavingLabel_of_opt hopt hB hj
  have hex : P.toLP.IsPivot B j (insert j (B.erase i)) :=
    ⟨hB, hj, hB.1.not_mem_of_mem_improving hj, i, hi, rfl⟩
  have huniq : ∀ B', P.toLP.IsPivot B j B' → B' = insert j (B.erase i) := by
    rintro B' ⟨-, -, -, i', hi', rfl⟩
    rw [P.toLP.isLeavingLabel_unique hnd hB hj hi' hi]
  have hpt : P.toLP.pivotTo B j = insert j (B.erase i) :=
    huniq _ (Classical.epsilon_spec (p := P.toLP.IsPivot B j) ⟨_, hex⟩)
  intro B'
  rw [hpt]
  exact ⟨huniq B', fun h ↦ h ▸ hex⟩

lemma pivotTo_hat_cap (hopt : ∃ x, P.toLP.IsOptimalSolution x)
    (hnd : ∀ B, P.toLP.IsFeasibleBasis B → P.toLP.IsNondegenerate B)
    {B : Finset (Fin n)} (hB : P.toLP.IsFeasibleBasis B) {j : Fin n}
    (hj : j ∈ P.toLP.improving B) :
    P.toLP.IsFeasibleBasis (P.toLP.pivotTo B j) ∧
    P.cap.toLP.pivotTo (hat B) (Fin.castSucc j) = hat (P.toLP.pivotTo B j) := by
  have hP := P.isPivot_iff_eq_pivotTo hopt hnd hB hj
  have hpiv : P.toLP.IsPivot B j (P.toLP.pivotTo B j) := (hP _).2 rfl
  have hfeas : P.toLP.IsFeasibleBasis (P.toLP.pivotTo B j) := by
    obtain ⟨-, -, -, i, hi, heq⟩ := hpiv
    rw [heq]; exact (P.toLP.pivot_spec hB hj hi).1
  have hQex : P.cap.toLP.IsPivot (hat B) j.castSucc (hat (P.toLP.pivotTo B j)) :=
    (P.isPivot_hat_cap_iff hopt hB _ _).2 ⟨j, _, rfl, hpiv, rfl⟩
  have hQ : P.cap.toLP.IsPivot (hat B) j.castSucc (P.cap.toLP.pivotTo (hat B) j.castSucc) :=
    Classical.epsilon_spec (p := P.cap.toLP.IsPivot (hat B) j.castSucc) ⟨_, hQex⟩
  obtain ⟨j', B', hjj, hB', heq⟩ := (P.isPivot_hat_cap_iff hopt hB _ _).1 hQ
  rw [Fin.castSucc_inj] at hjj
  subst hjj
  exact ⟨hfeas, by rw [heq, (hP B').1 hB']⟩

end IntLP

end WolfeSimplex
