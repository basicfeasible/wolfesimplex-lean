import WolfeSimplex.Defs.Scaling
import WolfeSimplex.Defs.HistoryRules
import WolfeSimplex.Proofs.RandomRuns
import WolfeSimplex.Proofs.CapFacts

/-!
# Scaling an LP (paper: Section 3 (`sec:equivalence`) (integrality discussion))

Multiplying the rows of `(A, b)` by positive numbers `r i` and `c` by `ω > 0` keeps the
feasible set, the bases, the basic solutions and directions and the ratio tests, and multiplies
every reduced cost by `ω`. Hence the pivots and the runs with all rules of Table 1
(`tab:wolfe-rules`) stay the same. Rational data can be scaled to integers this way.
-/

namespace WolfeSimplex

open Finset Matrix

variable {m n : ℕ}

namespace LP

variable (P : LP m n) {r : Fin m → ℝ} (hr : ∀ i, 0 < r i) (ω : ℝ)

theorem scale_mulVec (r : Fin m → ℝ) (x : Fin n → ℝ) :
    (P.scale r ω).A *ᵥ x = fun i ↦ r i * (P.A *ᵥ x) i := by
  funext i
  simp only [scale, mulVec, dotProduct, Matrix.of_apply, Finset.mul_sum, mul_assoc]

include hr

theorem scale_mulVec_eq_b_iff (x : Fin n → ℝ) :
    (P.scale r ω).A *ᵥ x = (P.scale r ω).b ↔ P.A *ᵥ x = P.b := by
  rw [scale_mulVec]
  constructor
  · intro h; funext i
    exact mul_left_cancel₀ (hr i).ne' (congrFun h i)
  · intro h; funext i; simp [scale, h]

theorem scale_mulVec_eq_zero_iff (x : Fin n → ℝ) :
    (P.scale r ω).A *ᵥ x = 0 ↔ P.A *ᵥ x = 0 := by
  rw [scale_mulVec]
  constructor
  · intro h; funext i
    have := congrFun h i
    simpa [(hr i).ne'] using this
  · intro h; funext i; simp [h]

theorem scale_isFeasible_iff (x : Fin n → ℝ) : (P.scale r ω).IsFeasible x ↔ P.IsFeasible x := by
  unfold IsFeasible
  rw [scale_mulVec_eq_b_iff P hr]

theorem scale_isBasicSolutionOf : (P.scale r ω).IsBasicSolutionOf = P.IsBasicSolutionOf := by
  funext B x
  unfold IsBasicSolutionOf
  rw [scale_mulVec_eq_b_iff P hr]

theorem scale_basicSol : (P.scale r ω).basicSol = P.basicSol := by
  funext B
  unfold basicSol
  rw [scale_isBasicSolutionOf P hr]

theorem scale_isBasicDirOf : (P.scale r ω).IsBasicDirOf = P.IsBasicDirOf := by
  funext B j d
  unfold IsBasicDirOf
  rw [scale_mulVec_eq_zero_iff P hr]

theorem scale_basicDir : (P.scale r ω).basicDir = P.basicDir := by
  funext B j
  unfold basicDir
  rw [scale_isBasicDirOf P hr]

theorem scale_isBasis_iff (B : Finset (Fin n)) : (P.scale r ω).IsBasis B ↔ P.IsBasis B := by
  unfold IsBasis
  rw [linIndep_iff, linIndep_iff]
  simp only [scale_mulVec_eq_zero_iff P hr]

theorem scale_isFeasibleBasis_iff (B : Finset (Fin n)) :
    (P.scale r ω).IsFeasibleBasis B ↔ P.IsFeasibleBasis B := by
  unfold IsFeasibleBasis
  rw [scale_isBasis_iff P hr, scale_basicSol P hr]

theorem scale_reducedCost {B : Finset (Fin n)} (hB : P.IsBasis B) (j : Fin n) :
    (P.scale r ω).reducedCost B j = ω * P.reducedCost B j := by
  have hB' : (P.scale r ω).IsBasis B := (scale_isBasis_iff P hr ω B).2 hB
  by_cases hj : j ∈ B
  · rw [hB.reducedCost_of_mem hj, hB'.reducedCost_of_mem hj, mul_zero]
  · rw [← hB.cost_basicDir hj, ← hB'.cost_basicDir hj, scale_basicDir P hr]
    simp only [scale, dotProduct, Finset.mul_sum, mul_assoc]

theorem scale_isLeavingLabel : (P.scale r ω).IsLeavingLabel = P.IsLeavingLabel := by
  funext B j i
  unfold IsLeavingLabel
  rw [scale_basicSol P hr, scale_basicDir P hr]

variable {ω} (hω : 0 < ω)
include hω

theorem scale_improving {B : Finset (Fin n)} (hB : P.IsBasis B) :
    (P.scale r ω).improving B = P.improving B := by
  ext j
  simp only [improving, mem_filter, mem_univ, true_and, scale_reducedCost P hr ω hB]
  constructor
  · intro h
    by_contra h'
    nlinarith [mul_nonneg hω.le (not_lt.1 h')]
  · intro h
    exact mul_neg_of_pos_of_neg hω h

theorem scale_isPivot_iff (B : Finset (Fin n)) (j : Fin n) (B' : Finset (Fin n)) :
    (P.scale r ω).IsPivot B j B' ↔ P.IsPivot B j B' := by
  unfold IsPivot
  rw [scale_isFeasibleBasis_iff P hr, scale_isLeavingLabel P hr]
  constructor
  · rintro ⟨hB, hj, rest⟩
    exact ⟨hB, by rwa [scale_improving P hr hω hB.1] at hj, rest⟩
  · rintro ⟨hB, hj, rest⟩
    exact ⟨hB, by rwa [scale_improving P hr hω hB.1], rest⟩

theorem scale_isPivot : (P.scale r ω).IsPivot = P.IsPivot := by
  funext B j B'
  exact propext (scale_isPivot_iff P hr hω B j B')

theorem scale_pivotTo : (P.scale r ω).pivotTo = P.pivotTo := by
  funext B j
  unfold pivotTo
  rw [scale_isPivot P hr hω]

/-! ### Runs -/

theorem scale_run_iff (ch' ch : Finset (Fin n) → Fin n → Prop)
    (hch : ∀ B, P.IsFeasibleBasis B → ∀ j, ch' B j ↔ ch B j) (f : ℕ) (B : ℕ → Finset (Fin n)) :
    (P.scale r ω).IsSimplexRunWith ch' f B ↔ P.IsSimplexRunWith ch f B := by
  unfold IsSimplexRunWith IsPartialSimplexRunWith
  simp only [scale_isFeasibleBasis_iff P hr, scale_isPivot P hr hω]
  constructor
  · rintro ⟨⟨hf, hp⟩, hl⟩
    refine ⟨⟨hf, fun k hk ↦ ?_⟩, ?_⟩
    · obtain ⟨j, hj, hpj⟩ := hp k hk
      exact ⟨j, (hch _ (hf k hk.le) j).1 hj, hpj⟩
    · rwa [scale_improving P hr hω (hf f le_rfl).1] at hl
  · rintro ⟨⟨hf, hp⟩, hl⟩
    refine ⟨⟨hf, fun k hk ↦ ?_⟩, ?_⟩
    · obtain ⟨j, hj, hpj⟩ := hp k hk
      exact ⟨j, (hch _ (hf k hk.le) j).2 hj, hpj⟩
    · rwa [scale_improving P hr hω (hf f le_rfl).1]

theorem scale_runHist_iff (ch' ch : List (Fin n) → Finset (Fin n) → Fin n → Prop)
    (hch : ∀ hist B, P.IsFeasibleBasis B → ∀ j, ch' hist B j ↔ ch hist B j) (f : ℕ)
    (B : ℕ → Finset (Fin n)) (J : ℕ → Fin n) :
    (P.scale r ω).IsSimplexRunWithHist ch' f B J ↔ P.IsSimplexRunWithHist ch f B J := by
  unfold IsSimplexRunWithHist IsPartialSimplexRunWithHist
  simp only [scale_isFeasibleBasis_iff P hr, scale_isPivot P hr hω]
  constructor
  · rintro ⟨⟨hf, hp⟩, hl⟩
    refine ⟨⟨hf, fun k hk ↦ ⟨(hch _ _ (hf k hk.le) _).1 (hp k hk).1, (hp k hk).2⟩⟩, ?_⟩
    rwa [scale_improving P hr hω (hf f le_rfl).1] at hl
  · rintro ⟨⟨hf, hp⟩, hl⟩
    refine ⟨⟨hf, fun k hk ↦ ⟨(hch _ _ (hf k hk.le) _).2 (hp k hk).1, (hp k hk).2⟩⟩, ?_⟩
    rwa [scale_improving P hr hω (hf f le_rfl).1]

theorem scale_dantzig_iff {B : Finset (Fin n)} (hB : P.IsFeasibleBasis B) (j : Fin n) :
    (P.scale r ω).IsDantzigChoice B j ↔ P.IsDantzigChoice B j := by
  unfold IsDantzigChoice
  rw [scale_improving P hr hω hB.1]
  simp only [scale_reducedCost P hr ω hB.1]
  constructor
  · rintro ⟨hj, h⟩
    exact ⟨hj, fun i hi ↦ le_of_mul_le_mul_left (h i hi) hω⟩
  · rintro ⟨hj, h⟩
    exact ⟨hj, fun i hi ↦ mul_le_mul_of_nonneg_left (h i hi) hω.le⟩

omit hr hω in
/-- A pivot from a feasible basis exists when the optimum is finite, so `pivotTo` is a
feasible basis. -/
theorem isFeasibleBasis_pivotTo' (Q : LP m n) (hopt : ∃ x, Q.IsOptimalSolution x)
    {B : Finset (Fin n)} (hB : Q.IsFeasibleBasis B) {j : Fin n} (hj : j ∈ Q.improving B) :
    Q.IsFeasibleBasis (Q.pivotTo B j) := by
  obtain ⟨i, hi⟩ := Q.exists_leavingLabel_of_opt hopt hB hj
  have hex : ∃ B', Q.IsPivot B j B' :=
    ⟨_, hB, hj, hB.1.not_mem_of_mem_improving hj, i, hi, rfl⟩
  obtain ⟨-, hj', -, i', hi', heq⟩ := Classical.epsilon_spec hex
  have : Q.pivotTo B j = insert j (B.erase i') := heq
  rw [this]
  exact (pivot_spec hB hj' hi').1

omit hω in
include hω in
theorem scale_randomRun (hopt : ∃ x, P.IsOptimalSolution x)
    (rule' : (B : Finset (Fin n)) → ((P.scale r ω).improving B).Nonempty → PMF (Fin n))
    (rule : (B : Finset (Fin n)) → (P.improving B).Nonempty → PMF (Fin n))
    (hrule : ∀ B, P.IsFeasibleBasis B → ∀ h h', rule' B h' = rule B h)
    (hsupp : ∀ B h, ∀ j ∈ (rule B h).support, j ∈ P.improving B) (k : ℕ) :
    ∀ B, P.IsFeasibleBasis B → (P.scale r ω).randomRun rule' k B = P.randomRun rule k B := by
  induction k with
  | zero => intro B _; rfl
  | succ k ih =>
    intro B hB
    have himp := scale_improving P hr hω hB.1
    rw [randomRun, randomRun]
    by_cases h : (P.improving B).Nonempty
    · have h' : ((P.scale r ω).improving B).Nonempty := by rwa [himp]
      rw [dite_eq_left h, dite_eq_left h', hrule B hB h h', scale_pivotTo P hr hω]
      refine pmf_bind_congr_support _ _ _ fun j hj ↦ ?_
      rw [ih _ (isFeasibleBasis_pivotTo' P hopt hB (hsupp B h j hj))]
    · have h' : ¬ ((P.scale r ω).improving B).Nonempty := by rwa [himp]
      rw [dite_eq_right h, dite_eq_right h']

end LP

theorem scale_runs_main (P : LP m n) {r : Fin m → ℝ} (hr : ∀ i, 0 < r i) {ω : ℝ} (hω : 0 < ω) :
    (∀ f B, (P.scale r ω).IsSimplexRunWith (P.scale r ω).IsDantzigChoice f B ↔
      P.IsSimplexRunWith P.IsDantzigChoice f B) ∧
    (∀ ρ f B, (P.scale r ω).IsSimplexRunWith ((P.scale r ω).IsBlandChoice ρ) f B ↔
      P.IsSimplexRunWith (P.IsBlandChoice ρ) f B) ∧
    (∀ f B J, (P.scale r ω).IsSimplexRunWithHist (P.scale r ω).IsZadehChoice f B J ↔
      P.IsSimplexRunWithHist P.IsZadehChoice f B J) ∧
    (∀ j₀ f B J,
      (P.scale r ω).IsSimplexRunWithHist ((P.scale r ω).IsCunninghamChoice j₀) f B J ↔
        P.IsSimplexRunWithHist (P.IsCunninghamChoice j₀) f B J) := by
  refine ⟨fun f B ↦ P.scale_run_iff hr hω _ _ (fun _ hB j ↦ P.scale_dantzig_iff hr hω hB j) f B,
    fun ρ f B ↦ P.scale_run_iff hr hω _ _ (fun _ hB j ↦ ?_) f B,
    fun f B J ↦ P.scale_runHist_iff hr hω _ _ (fun _ _ hB j ↦ ?_) f B J,
    fun j₀ f B J ↦ P.scale_runHist_iff hr hω _ _ (fun _ _ hB j ↦ ?_) f B J⟩
  · unfold LP.IsBlandChoice; rw [P.scale_improving hr hω hB.1]
  · unfold LP.IsZadehChoice; rw [P.scale_improving hr hω hB.1]
  · unfold LP.IsCunninghamChoice; rw [P.scale_improving hr hω hB.1]

theorem scale_random_runs_main (P : LP m n) {r : Fin m → ℝ} (hr : ∀ i, 0 < r i) {ω : ℝ}
    (hω : 0 < ω) (hopt : ∃ x, P.IsOptimalSolution x) (B : Finset (Fin n))
    (hB : P.IsFeasibleBasis B) (k : ℕ) :
    (P.scale r ω).randomRun (P.scale r ω).randomEdge k B = P.randomRun P.randomEdge k B ∧
    (P.scale r ω).randomBlandRun k B = P.randomBlandRun k B := by
  have hu : ∀ (s t : Finset (Fin n)) (hs : s.Nonempty) (ht : t.Nonempty), s = t →
      uniformOn s hs = uniformOn t ht := by
    rintro _ _ _ _ rfl; rfl
  have hf : ∀ (π : Equiv.Perm (Fin n)) (s t : Finset (Fin n)) (hs : s.Nonempty)
      (ht : t.Nonempty), s = t → firstInOrder π s hs = firstInOrder π t ht := by
    rintro _ _ _ _ _ rfl; rfl
  refine ⟨P.scale_randomRun hr hω hopt _ _ (fun B hB h h' ↦ ?_) (fun B h j hj ↦ ?_) k B hB, ?_⟩
  · exact hu _ _ _ _ (P.scale_improving hr hω hB.1)
  · exact mem_of_mem_support_uniformOn hj
  · unfold LP.randomBlandRun
    refine pmf_bind_congr_support _ _ _ fun π _ ↦ ?_
    refine P.scale_randomRun hr hω hopt _ _ (fun B hB h h' ↦ ?_) (fun B h j hj ↦ ?_) k B hB
    · unfold LP.blandBy
      rw [hf π _ _ h' h (P.scale_improving hr hω hB.1)]
    · unfold LP.blandBy at hj
      rw [PMF.support_pure, Set.mem_singleton_iff] at hj
      rw [hj]; exact firstInOrder_mem π _ h

/-! ### Rational data can be scaled to integers -/

theorem rat_mul_den_dvd {q : ℚ} {R : ℕ} (h : q.den ∣ R) :
    (R : ℝ) * (q : ℝ) = ((q.num * ((R / q.den : ℕ) : ℤ) : ℤ) : ℝ) := by
  have hd : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  rw [Rat.cast_def, Int.cast_mul, Int.cast_natCast, Nat.cast_div h hd]
  field_simp

theorem scale_integral_main (P : LP m n) (hA : ∀ i j, ∃ q : ℚ, P.A i j = q)
    (hb : ∀ i, ∃ q : ℚ, P.b i = q) (hc : ∀ j, ∃ q : ℚ, P.c j = q) :
    ∃ (r : Fin m → ℝ) (ω : ℝ) (Q : IntLP m n), (∀ i, 0 < r i) ∧ 0 < ω ∧
      Q.toLP = P.scale r ω := by
  choose qA hqA using hA
  choose qb hqb using hb
  choose qc hqc using hc
  set R : Fin m → ℕ := fun i ↦ (∏ j, (qA i j).den) * (qb i).den
  set W : ℕ := ∏ j, (qc j).den
  have hR : ∀ i, 0 < R i := fun i ↦
    Nat.mul_pos (Finset.prod_pos fun j _ ↦ (qA i j).den_pos) (qb i).den_pos
  have hW : 0 < W := Finset.prod_pos fun j _ ↦ (qc j).den_pos
  have hdA : ∀ i j, (qA i j).den ∣ R i := fun i j ↦
    dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem _ (mem_univ j)) _
  have hdb : ∀ i, (qb i).den ∣ R i := fun i ↦ dvd_mul_left _ _
  have hdc : ∀ j, (qc j).den ∣ W := fun j ↦ Finset.dvd_prod_of_mem _ (mem_univ j)
  refine ⟨fun i ↦ (R i : ℝ), (W : ℝ),
    ⟨fun i j ↦ (qA i j).num * ((R i / (qA i j).den : ℕ) : ℤ),
     fun i ↦ (qb i).num * ((R i / (qb i).den : ℕ) : ℤ),
     fun j ↦ (qc j).num * ((W / (qc j).den : ℕ) : ℤ)⟩,
    fun i ↦ Nat.cast_pos.2 (hR i), Nat.cast_pos.2 hW, ?_⟩
  simp only [IntLP.toLP, LP.scale]
  congr 1
  · ext i j
    simp only [Matrix.of_apply, hqA]
    exact (rat_mul_den_dvd (hdA i j)).symm
  · funext i
    rw [hqb]
    exact (rat_mul_den_dvd (hdb i)).symm
  · funext j
    rw [hqc]
    exact (rat_mul_den_dvd (hdc j)).symm

end WolfeSimplex
