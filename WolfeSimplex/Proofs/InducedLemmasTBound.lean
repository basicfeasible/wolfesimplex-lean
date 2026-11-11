import WolfeSimplex.Proofs.Hat

/-!
# Lemma 8 (`lem:T-bound`) for all feasible points

* `LP.exists_basis_superset`: linearly independent columns extend to a basis
  (when `rank A = m`).
* `LP.exists_feasibleBasis_sum_ge`: over a nonempty bounded feasible set, the
  maximum of `1ᵀx` is attained at a basic feasible solution (support reduction).
* `T_bound_main`: Lemma 8 (`lem:T-bound`), `2 · 1ᵀx < T` for every feasible `x`.
-/

namespace WolfeSimplex

open Finset Matrix

variable {m n : ℕ}

/-- Extension of linearly independent columns to a basis (needs rank A = m). -/
theorem LP.exists_basis_superset (P : LP m n) (hrank : P.A.rank = m) (B₀ : Finset (Fin n))
    (hB₀ : LinearIndependent ℝ (fun j : B₀ ↦ P.col (j : Fin n))) :
    ∃ B, B₀ ⊆ B ∧ P.IsBasis B := by
  classical
  have hs : LinearIndepOn ℝ P.col (B₀ : Set (Fin n)) := hB₀
  obtain ⟨b, -, hsb, hspan, hli⟩ := exists_linearIndepOn_extension hs (Set.subset_univ _)
  have hLI : LinearIndependent ℝ (fun j : b.toFinset ↦ P.col (j : Fin n)) := by
    have h : LinearIndepOn ℝ P.col ((b.toFinset : Finset (Fin n)) : Set (Fin n)) := by
      rwa [Set.coe_toFinset]
    exact h
  refine ⟨b.toFinset, ?_, ?_, hLI⟩
  · intro j hj
    simpa using hsb (Finset.mem_coe.2 hj)
  · have hcard := finrank_span_eq_card hLI
    rw [Fintype.card_coe] at hcard
    have hcol : P.col = P.A.col := rfl
    have hrange : Set.range (fun j : b.toFinset ↦ P.col (j : Fin n)) = P.col '' b := by
      ext v
      simp [Set.mem_image]
    have hspan_eq : Submodule.span ℝ (Set.range (fun j : b.toFinset ↦ P.col (j : Fin n))) =
        Submodule.span ℝ (Set.range P.A.col) := by
      apply le_antisymm
      · apply Submodule.span_mono
        rintro v ⟨j, rfl⟩
        exact ⟨j, rfl⟩
      · rw [Submodule.span_le, hrange]
        rintro v ⟨j, rfl⟩
        exact hspan ⟨j, Set.mem_univ _, rfl⟩
    rw [hspan_eq, ← Matrix.rank_eq_finrank_span_cols, hrank] at hcard
    exact hcard.symm

namespace LP

variable (P : LP m n)

/-- A bounded nonempty feasible set has no nonzero nonnegative direction `w` with
`A w = 0`. -/
theorem eq_zero_of_nonneg_dir (hbdd : P.FeasibleSetNonemptyBounded) {x : Fin n → ℝ}
    (hx : P.IsFeasible x) {w : Fin n → ℝ} (hAw : P.A *ᵥ w = 0) (hw : ∀ j, 0 ≤ w j) :
    w = 0 := by
  obtain ⟨R, hR⟩ := hbdd.2
  funext k
  by_contra hk
  have hwk : 0 < w k := lt_of_le_of_ne (hw k) (Ne.symm hk)
  set t : ℝ := (|R| + 1) / w k with ht
  have ht0 : 0 ≤ t := div_nonneg (by positivity) hwk.le
  have hfeas : P.IsFeasible (x + t • w) := by
    refine ⟨?_, fun j ↦ ?_⟩
    · rw [Matrix.mulVec_add, Matrix.mulVec_smul, hAw, smul_zero, add_zero, hx.1]
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact add_nonneg (hx.2 j) (mul_nonneg ht0 (hw j))
  have h1 := (le_abs_self _).trans (hR _ hfeas k)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1
  have h2 : t * w k = |R| + 1 := by rw [ht]; field_simp
  have := hx.2 k
  have := le_abs_self R
  linarith

/-- The maximum of 1ᵀx over a bounded feasible set is attained at a basic feasible solution. -/
theorem exists_feasibleBasis_sum_ge (P : LP m n) (hrank : P.A.rank = m)
    (hbdd : P.FeasibleSetNonemptyBounded) (x : Fin n → ℝ) (hx : P.IsFeasible x) :
    ∃ B, P.IsFeasibleBasis B ∧ ∑ j, x j ≤ ∑ j, P.basicSol B j := by
  classical
  induction hk : (univ.filter (fun j ↦ x j ≠ 0)).card using Nat.strong_induction_on
    generalizing x with
  | _ k ih =>
  set S := univ.filter (fun j ↦ x j ≠ 0) with hS
  have hoff : ∀ j ∉ S, x j = 0 := fun j hj ↦ by simpa [hS] using hj
  by_cases hind : LinearIndependent ℝ (fun j : S ↦ P.col (j : Fin n))
  · obtain ⟨B, hSB, hB⟩ := P.exists_basis_superset hrank S hind
    have hxB : x = P.basicSol B := hB.eq_basicSol hx.1 (fun j hj ↦ hoff j (fun h ↦ hj (hSB h)))
    refine ⟨B, ⟨hB, fun j ↦ hxB ▸ hx.2 j⟩, ?_⟩
    rw [← hxB]
  · -- a nonzero `z` vanishing off `S` with `A z = 0`
    have hz' : ∃ z : Fin n → ℝ, (∀ j ∉ S, z j = 0) ∧ P.A *ᵥ z = 0 ∧ z ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hind ((linIndep_iff P S).2 fun z h1 h2 ↦ by
        by_contra h3; exact h3 (hcon z h1 h2))
    obtain ⟨z₀, hz₀off, hAz₀, hz₀ne⟩ := hz'
    -- every nonzero such direction has a negative coordinate
    have hneg : ∀ w : Fin n → ℝ, P.A *ᵥ w = 0 → w ≠ 0 → ∃ j, w j < 0 := by
      intro w hAw hw
      by_contra hcon
      push Not at hcon
      exact hw (P.eq_zero_of_nonneg_dir hbdd hx hAw hcon)
    -- choose the sign with `∑ z ≥ 0`
    obtain ⟨z, hzoff, hAz, hzneg, hzsum⟩ : ∃ z : Fin n → ℝ, (∀ j ∉ S, z j = 0) ∧
        P.A *ᵥ z = 0 ∧ (∃ j, z j < 0) ∧ 0 ≤ ∑ j, z j := by
      by_cases hsum : 0 ≤ ∑ j, z₀ j
      · exact ⟨z₀, hz₀off, hAz₀, hneg z₀ hAz₀ hz₀ne, hsum⟩
      · refine ⟨-z₀, fun j hj ↦ by simp [hz₀off j hj], by rw [Matrix.mulVec_neg, hAz₀, neg_zero],
          hneg _ (by rw [Matrix.mulVec_neg, hAz₀, neg_zero]) (neg_ne_zero.2 hz₀ne), ?_⟩
        simp only [Pi.neg_apply, Finset.sum_neg_distrib]
        linarith
    -- the ratio test
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
    have hsub : univ.filter (fun j ↦ x' j ≠ 0) ⊂ S := by
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
    have hlt : (univ.filter (fun j ↦ x' j ≠ 0)).card < k := hk ▸ Finset.card_lt_card hsub
    obtain ⟨B, hB, hsumB⟩ := ih _ hlt x' hx'feas rfl
    refine ⟨B, hB, le_trans ?_ hsumB⟩
    have : ∑ j, x' j = ∑ j, x j + t * ∑ j, z j := by
      simp [hx', Finset.sum_add_distrib, Finset.mul_sum]
    rw [this]
    nlinarith

end LP

/-- Lemma 8 (`lem:T-bound`). -/
theorem T_bound_main (P : IntLP m n) (hP : P.IsAdmissible) (x : Fin n → ℝ)
    (hx : P.toLP.IsFeasible x) : 2 * ∑ j, x j < P.T := by
  obtain ⟨B, hB, hsum⟩ := P.toLP.exists_feasibleBasis_sum_ge hP.2.1 hP.2.2.1 x hx
  have h := IntLP.two_mul_sum_xB_lt hB.1
  simp only [IntLP.xB] at h
  linarith

end WolfeSimplex
