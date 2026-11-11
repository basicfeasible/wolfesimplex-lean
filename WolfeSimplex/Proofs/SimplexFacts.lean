import WolfeSimplex.Defs.Simplex

/-!
# General facts about bases and the simplex method

Lemma 7 (`lem:identities`) and the facts stated in Section 2.1 (`sec:simplex`)
(pivots, optimality).
-/

namespace WolfeSimplex.LP

open Finset Matrix

variable {m n : ℕ} (P : LP m n)

/-- The solution of `A x = r` that vanishes outside `B` (unique for a basis). -/
noncomputable def solOn (B : Finset (Fin n)) (r : Fin m → ℝ) : Fin n → ℝ :=
  Classical.epsilon (fun x ↦ P.A *ᵥ x = r ∧ ∀ j ∉ B, x j = 0)

theorem basicSol_eq_solOn (B : Finset (Fin n)) : P.basicSol B = P.solOn B P.b := rfl

/-- `A x = ∑_j x_j A_j`. -/
theorem mulVec_eq_sum (x : Fin n → ℝ) : P.A *ᵥ x = ∑ j, x j • P.col j := by
  ext i
  simp [mulVec, dotProduct, col, Finset.sum_apply, mul_comm]

/-- `A x = ∑_{j ∈ B} x_j A_j` (as a sum over the subtype `B`) if `x` vanishes off `B`. -/
theorem mulVec_eq_sum_subtype {B : Finset (Fin n)} {x : Fin n → ℝ}
    (hx : ∀ j ∉ B, x j = 0) : P.A *ᵥ x = ∑ j : B, x j • P.col j := by
  rw [mulVec_eq_sum, Finset.sum_coe_sort B (fun j ↦ x j • P.col j)]
  symm
  apply Finset.sum_subset (subset_univ B)
  intro k _ hk
  simp [hx k hk]

/-- Linear independence of the columns `A_j`, `j ∈ B`, in vector form. -/
theorem linIndep_iff (B : Finset (Fin n)) :
    LinearIndependent ℝ (fun j : B ↦ P.col (j : Fin n)) ↔
      ∀ x : Fin n → ℝ, (∀ j ∉ B, x j = 0) → P.A *ᵥ x = 0 → x = 0 := by
  rw [Fintype.linearIndependent_iff]
  constructor
  · intro h x hx hAx
    rw [mulVec_eq_sum_subtype P hx] at hAx
    have h' := h (fun j ↦ x j) hAx
    funext k
    by_cases hk : k ∈ B
    · exact h' ⟨k, hk⟩
    · exact hx k hk
  · intro h g hg i
    let x : Fin n → ℝ := fun k ↦ if hk : k ∈ B then g ⟨k, hk⟩ else 0
    have hx : ∀ j ∉ B, x j = 0 := fun j hj ↦ by simp [x, hj]
    have hAx : P.A *ᵥ x = 0 := by
      rw [mulVec_eq_sum_subtype P hx, ← hg]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      simp [x]
    have := congrFun (h x hx hAx) i
    simpa [x] using this

/-- `A e_j = A_j`. -/
theorem mulVec_single_one (j : Fin n) : P.A *ᵥ Pi.single j 1 = P.col j := by
  ext i
  simp [mulVec, dotProduct, col, Pi.single_apply]

variable {P}

/-- The columns of a basis, as a basis of `ℝ^m`. -/
noncomputable def IsBasis.colBasis {B : Finset (Fin n)} (hB : P.IsBasis B) :
    Module.Basis B ℝ (Fin m → ℝ) :=
  basisOfLinearIndependentOfCardEqFinrank' (fun j : B ↦ P.col (j : Fin n)) hB.2
    (by rw [Fintype.card_coe, hB.1, Module.finrank_fin_fun])

theorem IsBasis.colBasis_apply {B : Finset (Fin n)} (hB : P.IsBasis B) (j : B) :
    hB.colBasis j = P.col j := by
  simp [IsBasis.colBasis]

/-- The columns of a basis are linearly independent, in vector form. -/
theorem IsBasis.eq_zero {B : Finset (Fin n)} (hB : P.IsBasis B) {x : Fin n → ℝ}
    (hx : ∀ j ∉ B, x j = 0) (hAx : P.A *ᵥ x = 0) : x = 0 :=
  (linIndep_iff P B).1 hB.2 x hx hAx

theorem IsBasis.exists_sol {B : Finset (Fin n)} (hB : P.IsBasis B) (r : Fin m → ℝ) :
    ∃ x : Fin n → ℝ, P.A *ᵥ x = r ∧ ∀ j ∉ B, x j = 0 := by
  let bas := hB.colBasis
  let x : Fin n → ℝ := fun k ↦ if hk : k ∈ B then bas.repr r ⟨k, hk⟩ else 0
  have hx : ∀ j ∉ B, x j = 0 := fun j hj ↦ by simp [x, hj]
  refine ⟨x, ?_, hx⟩
  rw [mulVec_eq_sum_subtype P hx]
  conv_rhs => rw [← bas.sum_repr r]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp [x, bas, IsBasis.colBasis_apply]

theorem IsBasis.solOn_spec {B : Finset (Fin n)} (hB : P.IsBasis B) (r : Fin m → ℝ) :
    P.A *ᵥ P.solOn B r = r ∧ ∀ j ∉ B, P.solOn B r j = 0 :=
  Classical.epsilon_spec (hB.exists_sol r)

theorem IsBasis.eq_solOn {B : Finset (Fin n)} (hB : P.IsBasis B) {r : Fin m → ℝ}
    {x : Fin n → ℝ} (hAx : P.A *ᵥ x = r) (hx : ∀ j ∉ B, x j = 0) : x = P.solOn B r := by
  obtain ⟨h1, h2⟩ := hB.solOn_spec r
  have h := hB.eq_zero (x := x - P.solOn B r)
    (fun j hj ↦ by simp [hx j hj, h2 j hj]) (by rw [mulVec_sub, hAx, h1, sub_self])
  exact sub_eq_zero.1 h

/-- Lemma 7 (`lem:identities`)(b), first part. -/
theorem IsBasis.basicSol_spec {B : Finset (Fin n)} (hB : P.IsBasis B) :
    P.IsBasicSolutionOf B (P.basicSol B) :=
  hB.solOn_spec P.b

theorem IsBasis.eq_basicSol {B : Finset (Fin n)} (hB : P.IsBasis B) {x : Fin n → ℝ}
    (hAx : P.A *ᵥ x = P.b) (hx : ∀ j ∉ B, x j = 0) : x = P.basicSol B :=
  hB.eq_solOn hAx hx

theorem IsBasis.dualVec_spec {B : Finset (Fin n)} (hB : P.IsBasis B) :
    P.IsDualVectorOf B (P.dualVec B) := by
  apply Classical.epsilon_spec (p := P.IsDualVectorOf B)
  let f : (Fin m → ℝ) →ₗ[ℝ] ℝ := hB.colBasis.constr ℝ (fun j : B ↦ P.c j)
  refine ⟨fun i ↦ f (fun k ↦ if i = k then 1 else 0), fun j hj ↦ ?_⟩
  have h1 : f (P.col j) = P.c j := by
    rw [← hB.colBasis_apply ⟨j, hj⟩]
    simp [f]
  rw [← h1, LinearMap.pi_apply_eq_sum_univ f (P.col j), dotProduct]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp [smul_eq_mul, mul_comm]

/-- Lemma 7 (`lem:identities`)(a). -/
theorem IsBasis.reducedCost_of_mem {B : Finset (Fin n)} (hB : P.IsBasis B) {i : Fin n}
    (hi : i ∈ B) : P.reducedCost B i = 0 := by
  simp [reducedCost, hB.dualVec_spec i hi]

theorem IsBasis.not_mem_of_mem_improving {B : Finset (Fin n)} (hB : P.IsBasis B)
    {j : Fin n} (hj : j ∈ P.improving B) : j ∉ B := by
  intro hjB
  have : P.reducedCost B j < 0 := by simpa [improving] using hj
  rw [hB.reducedCost_of_mem hjB] at this
  exact lt_irrefl _ this

/-- Lemma 7 (`lem:identities`)(c), first part. -/
theorem IsBasis.basicDir_spec {B : Finset (Fin n)} (hB : P.IsBasis B) {j : Fin n}
    (hj : j ∉ B) : P.IsBasicDirOf B j (P.basicDir B j) := by
  apply Classical.epsilon_spec (p := P.IsBasicDirOf B j)
  obtain ⟨h1, h2⟩ := hB.solOn_spec (-P.col j)
  refine ⟨P.solOn B (-P.col j) + Pi.single j 1, ?_, ?_, ?_⟩
  · rw [mulVec_add, h1, mulVec_single_one, neg_add_cancel]
  · simp [h2 j hj]
  · intro k hk hkj
    simp [h2 k hk, hkj]

-- `hB` is not needed for this identity; it is kept in the approved statement.
set_option linter.unusedVariables false in
/-- `cᵀx = (y^B)ᵀ(Ax) + ∑_k c̄^B_k x_k` for every `x`. -/
theorem IsBasis.cost_eq {B : Finset (Fin n)} (hB : P.IsBasis B) (x : Fin n → ℝ) :
    P.c ⬝ᵥ x = P.dualVec B ⬝ᵥ (P.A *ᵥ x) + ∑ k, P.reducedCost B k * x k := by
  rw [dotProduct_mulVec, dotProduct, dotProduct, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [reducedCost, vecMul, dotProduct, col]
  ring

/-- Lemma 7 (`lem:identities`)(c), second part: `cᵀ d^{B,j} = c̄^B_j`. -/
theorem IsBasis.cost_basicDir {B : Finset (Fin n)} (hB : P.IsBasis B) {j : Fin n}
    (hj : j ∉ B) : P.c ⬝ᵥ P.basicDir B j = P.reducedCost B j := by
  obtain ⟨h1, h2, h3⟩ := hB.basicDir_spec hj
  rw [hB.cost_eq, h1, dotProduct_zero, zero_add, Finset.sum_eq_single j, h2, mul_one]
  · intro k _ hkj
    by_cases hk : k ∈ B
    · simp [hB.reducedCost_of_mem hk]
    · simp [h3 k hk hkj]
  · simp

/-- Lemma 7 (`lem:identities`)(b), second part: `z_B = (y^B)ᵀ b`. -/
theorem IsBasis.objValue_eq {B : Finset (Fin n)} (hB : P.IsBasis B) :
    P.c ⬝ᵥ P.basicSol B = P.dualVec B ⬝ᵥ P.b := by
  obtain ⟨h1, h2⟩ := hB.basicSol_spec
  rw [hB.cost_eq, h1, Finset.sum_eq_zero, add_zero]
  intro k _
  by_cases hk : k ∈ B
  · simp [hB.reducedCost_of_mem hk]
  · simp [h2 k hk]

/-- The basic direction is nonnegative outside `B`. -/
theorem IsBasis.basicDir_nonneg_of_not_mem {B : Finset (Fin n)} (hB : P.IsBasis B)
    {j : Fin n} (hj : j ∉ B) {k : Fin n} (hk : k ∉ B) : 0 ≤ P.basicDir B j k := by
  obtain ⟨_, h2, h3⟩ := hB.basicDir_spec hj
  by_cases hkj : k = j
  · rw [hkj, h2]; exact zero_le_one
  · rw [h3 k hk hkj]

/-- `A (x^B + r d^{B,j}) = b`. -/
theorem IsBasis.mulVec_add_smul_basicDir {B : Finset (Fin n)} (hB : P.IsBasis B)
    {j : Fin n} (hj : j ∉ B) (r : ℝ) :
    P.A *ᵥ (P.basicSol B + r • P.basicDir B j) = P.b := by
  rw [mulVec_add, mulVec_smul, (hB.basicDir_spec hj).1, hB.basicSol_spec.1, smul_zero,
    add_zero]

/-- In a bounded LP, the pivot on an improving label has a leaving label. -/
theorem exists_leavingLabel (hbdd : P.FeasibleSetNonemptyBounded) {B : Finset (Fin n)}
    (hB : P.IsFeasibleBasis B) {j : Fin n} (hj : j ∈ P.improving B) :
    ∃ i, P.IsLeavingLabel B j i := by
  have hjB := hB.1.not_mem_of_mem_improving hj
  set x := P.basicSol B
  set d := P.basicDir B j
  set S := B.filter (fun k ↦ d k < 0) with hS
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · exfalso
    obtain ⟨R, hR⟩ := hbdd.2
    have hd : ∀ k, 0 ≤ d k := by
      intro k
      by_cases hk : k ∈ B
      · by_contra hneg
        have : k ∈ S := by simp [hS, hk, not_le.1 hneg]
        rw [hSe] at this
        exact absurd this (Finset.notMem_empty k)
      · exact hB.1.basicDir_nonneg_of_not_mem hjB hk
    set r := |R| + 1
    have hr : 0 ≤ r := by positivity
    have hfeas : P.IsFeasible (x + r • d) :=
      ⟨hB.1.mulVec_add_smul_basicDir hjB r,
        fun k ↦ by simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
                   exact add_nonneg (hB.2 k) (mul_nonneg hr (hd k))⟩
    have h := hR _ hfeas j
    have hxj : x j = 0 := hB.1.basicSol_spec.2 j hjB
    have hdj : d j = 1 := (hB.1.basicDir_spec hjB).2.1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hxj, hdj, mul_one, zero_add] at h
    have : |R| + 1 ≤ R := le_trans (le_abs_self _) h
    linarith [le_abs_self R]
  · obtain ⟨i, hiS, hmin⟩ := Finset.exists_min_image S (fun k ↦ x k / (-d k)) hSne
    simp only [hS, Finset.mem_filter] at hiS hmin
    exact ⟨i, hiS.1, hiS.2, fun k hk hdk ↦ hmin k ⟨hk, hdk⟩⟩

/-- Equation 3 (`eq:pivot`): the pivot gives a feasible basis whose basic solution is
`x^B + θ d^{B,j}` with `θ = x^B_i / (-d^{B,j}_i)`. -/
theorem pivot_spec {B : Finset (Fin n)} (hB : P.IsFeasibleBasis B) {j : Fin n}
    (hj : j ∈ P.improving B) {i : Fin n} (hi : P.IsLeavingLabel B j i) :
    P.IsFeasibleBasis (insert j (B.erase i)) ∧
    P.basicSol (insert j (B.erase i)) =
      P.basicSol B + (P.basicSol B i / (-P.basicDir B j i)) • P.basicDir B j := by
  have hjB := hB.1.not_mem_of_mem_improving hj
  obtain ⟨hiB, hdi, hmin⟩ := hi
  obtain ⟨hAd, hdj, hd0⟩ := hB.1.basicDir_spec hjB
  obtain ⟨hAx, hx0⟩ := hB.1.basicSol_spec
  set x := P.basicSol B
  set d := P.basicDir B j
  set θ := x i / (-d i) with hθ
  set B' := insert j (B.erase i) with hB'
  have hij : i ≠ j := fun h ↦ hjB (h ▸ hiB)
  have hθ0 : 0 ≤ θ := div_nonneg (hB.2 i) (by linarith)
  -- the new point
  have hx'i : x i + θ * d i = 0 := by
    have hne : d i ≠ 0 := ne_of_lt hdi
    rw [hθ, div_neg, neg_mul, div_mul_cancel₀ _ hne, add_neg_cancel]
  have hx'0 : ∀ k ∉ B', (x + θ • d) k = 0 := by
    intro k hk
    simp only [hB', Finset.mem_insert, Finset.mem_erase, not_or, not_and_or, not_not] at hk
    obtain ⟨hkj, hk⟩ := hk
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases hk with hki | hkB
    · rw [hki]; exact hx'i
    · rw [hx0 k hkB, hd0 k hkB hkj]; ring
  have hx'nn : ∀ k, 0 ≤ (x + θ • d) k := by
    intro k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hk : k ∈ B ∧ d k < 0
    · have h := hmin k hk.1 hk.2
      have h' : θ * (-d k) ≤ x k := (le_div_iff₀ (by linarith [hk.2])).1 h
      linarith
    · have hdk : 0 ≤ d k := by
        by_cases hkB : k ∈ B
        · exact le_of_not_gt fun h ↦ hk ⟨hkB, h⟩
        · exact hB.1.basicDir_nonneg_of_not_mem hjB hkB
      exact add_nonneg (hB.2 k) (mul_nonneg hθ0 hdk)
  -- `B'` is a basis
  have hcard : B'.card = m := by
    have hjE : j ∉ B.erase i := fun h ↦ hjB (Finset.mem_of_mem_erase h)
    have hpos : 0 < B.card := Finset.card_pos.2 ⟨i, hiB⟩
    rw [hB', Finset.card_insert_of_notMem hjE, Finset.card_erase_of_mem hiB, ← hB.1.1]
    omega
  have hiB' : i ∉ B' := by
    simp [hB', hij]
  have hli : LinearIndependent ℝ (fun k : B' ↦ P.col (k : Fin n)) := by
    rw [linIndep_iff]
    intro β hβ hAβ
    set γ := β - β j • d with hγ
    have hγ0 : ∀ k ∉ B, γ k = 0 := by
      intro k hk
      simp only [hγ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      by_cases hkj : k = j
      · rw [hkj, hdj]; ring
      · have hkB' : k ∉ B' := by simp [hB', hkj, hk]
        rw [hβ k hkB', hd0 k hk hkj]; ring
    have hAγ : P.A *ᵥ γ = 0 := by
      rw [hγ, mulVec_sub, mulVec_smul, hAβ, hAd, smul_zero, sub_zero]
    have hγz := hB.1.eq_zero hγ0 hAγ
    have hγi := congrFun hγz i
    simp only [hγ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hβ i hiB', Pi.zero_apply,
      zero_sub, neg_eq_zero, mul_eq_zero] at hγi
    have hβj : β j = 0 := by
      rcases hγi with h | h
      · exact h
      · exact absurd h (ne_of_lt hdi)
    have : β = γ := by rw [hγ, hβj, zero_smul, sub_zero]
    rw [this, hγz]
  have hbas : P.IsBasis B' := ⟨hcard, hli⟩
  have heq := hbas.eq_basicSol (hB.1.mulVec_add_smul_basicDir hjB θ) hx'0
  refine ⟨⟨hbas, fun k ↦ ?_⟩, heq.symm⟩
  rw [← heq]
  exact hx'nn k

/-- A nondegenerate feasible basis is optimal if and only if it has no improving
label (Section 2.1 (`sec:simplex`)). -/
theorem optimal_iff {B : Finset (Fin n)} (hB : P.IsFeasibleBasis B)
    (hnd : P.IsNondegenerate B) : P.IsOptimalBasis B ↔ P.improving B = ∅ := by
  constructor
  · intro hopt
    by_contra hne
    obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.2 hne
    have hjB := hB.1.not_mem_of_mem_improving hj
    have hrc : P.reducedCost B j < 0 := by simpa [improving] using hj
    set x := P.basicSol B
    set d := P.basicDir B j
    have hev : ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ k, 0 ≤ x k + r * d k := by
      rw [Filter.eventually_all]
      intro k
      by_cases hk : k ∈ B
      · have hc : Continuous fun r : ℝ ↦ x k + r * d k := by fun_prop
        have h0 : (0 : ℝ) < x k + 0 * d k := by simpa using hnd k hk
        have := hc.continuousAt.eventually (lt_mem_nhds h0)
        exact (this.filter_mono nhdsWithin_le_nhds).mono fun r hr ↦ le_of_lt hr
      · refine eventually_nhdsWithin_of_forall fun r hr ↦ ?_
        have hxk : x k = 0 := hB.1.basicSol_spec.2 k hk
        rw [hxk, zero_add]
        exact mul_nonneg (le_of_lt hr) (hB.1.basicDir_nonneg_of_not_mem hjB hk)
    obtain ⟨r, hr, hrpos⟩ := (hev.and self_mem_nhdsWithin).exists
    have hfeas : P.IsFeasible (x + r • d) :=
      ⟨hB.1.mulVec_add_smul_basicDir hjB r, fun k ↦ by simpa using hr k⟩
    have h := hopt.2.2 _ hfeas
    rw [dotProduct_add, dotProduct_smul, hB.1.cost_basicDir hjB, smul_eq_mul] at h
    have : 0 < r * -P.reducedCost B j := mul_pos hrpos (by linarith)
    linarith
  · intro hemp
    refine ⟨hB, ⟨hB.1.basicSol_spec.1, hB.2⟩, fun y hy ↦ ?_⟩
    have hrc : ∀ k, 0 ≤ P.reducedCost B k := by
      intro k
      by_contra hneg
      have : k ∈ P.improving B := by simp [improving, not_le.1 hneg]
      rw [hemp] at this
      exact Finset.notMem_empty k this
    rw [hB.1.objValue_eq, hB.1.cost_eq y, hy.1, le_add_iff_nonneg_right]
    exact Finset.sum_nonneg fun k _ ↦ mul_nonneg (hrc k) (hy.2 k)

end WolfeSimplex.LP
