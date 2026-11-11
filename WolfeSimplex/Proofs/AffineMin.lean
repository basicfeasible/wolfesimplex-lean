import WolfeSimplex.Proofs.WolfeFacts
import WolfeSimplex.Defs.Rules

/-!
# Lemma 1 (`lem:affine-min`) and the well-definedness of Wolfe's method

Proofs of `affine_min` (Lemma 1 (`lem:affine-min`) together with the existence and
uniqueness of `w_S` and `λ^{*S}`) and of `wolfe_well_defined` (Section 2.2 (`sec:wolfe`)
and the termination discussion in Section 2.2 (`sec:wolfe`)).
-/

namespace WolfeSimplex

open Finset Matrix

namespace Wolfe

variable {N D : ℕ} (p : Fin N → Fin D → ℝ)

/-! ### Elementary facts -/

theorem sum_smul_dotProduct (S : Finset (Fin N)) (lam : Fin N → ℝ) (v : Fin D → ℝ) :
    (∑ i ∈ S, lam i • p i) ⬝ᵥ v = ∑ i ∈ S, lam i * (p i ⬝ᵥ v) := by
  rw [sum_dotProduct]
  simp [smul_dotProduct]

/-- Existence of a point of `aff(S)` with zero gaps on `S` (solution of the KKT system
of the affine minimization problem). -/
theorem exists_gap_zero {S : Finset (Fin N)} (hS : S.Nonempty)
    (hAI : IsAffinelyIndependent p S) :
    ∃ lam : Fin N → ℝ, (∀ i ∉ S, lam i = 0) ∧ ∑ i ∈ S, lam i = 1 ∧
      ∀ i ∈ S, gap p i (∑ k ∈ S, lam k • p k) = 0 := by
  classical
  let L : ((Fin N → ℝ) × ℝ) →ₗ[ℝ] ((Fin N → ℝ) × ℝ) :=
    { toFun := fun x ↦ (fun i ↦ if i ∈ S then p i ⬝ᵥ (∑ k ∈ S, x.1 k • p k) + x.2 else x.1 i,
        ∑ i ∈ S, x.1 i)
      map_add' := by
        rintro ⟨a, s⟩ ⟨b, t⟩
        refine Prod.ext (funext fun i ↦ ?_) ?_
        · simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul, sum_add_distrib,
            dotProduct_add]
          split_ifs <;> ring
        · simp [sum_add_distrib]
      map_smul' := by
        rintro c ⟨a, s⟩
        refine Prod.ext (funext fun i ↦ ?_) ?_
        · simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, mul_smul,
            ← smul_sum, dotProduct_smul, RingHom.id_apply]
          split_ifs <;> ring
        · simp [mul_sum] }
  have hL : ∀ x, L x = (fun i ↦ if i ∈ S then p i ⬝ᵥ (∑ k ∈ S, x.1 k • p k) + x.2 else x.1 i,
      ∑ i ∈ S, x.1 i) := fun x ↦ rfl
  have hinj : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨a, t⟩ h
    rw [hL] at h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [Prod.fst_zero, Prod.snd_zero] at h1 h2
    have hS' : ∀ i ∈ S, p i ⬝ᵥ (∑ k ∈ S, a k • p k) = -t := fun i hi ↦ by
      have := congrFun h1 i
      simp only [ite_eq_left hi, Pi.zero_apply] at this
      linarith
    have hout : ∀ i ∉ S, a i = 0 := fun i hi ↦ by
      have := congrFun h1 i
      simpa [hi] using this
    set w := ∑ k ∈ S, a k • p k with hw
    have hww : w ⬝ᵥ w = 0 := by
      conv_lhs => rw [hw]
      rw [sum_smul_dotProduct, sum_congr rfl fun i hi ↦ by rw [hS' i hi], ← sum_mul, h2,
        zero_mul]
    have hw0 : w = 0 := dotProduct_self_eq_zero.mp hww
    have ha : ∀ i ∈ S, a i = 0 := hAI a (hw ▸ hw0) h2
    have haz : a = 0 := funext fun i ↦ by
      by_cases hi : i ∈ S
      · exact ha i hi
      · exact hout i hi
    obtain ⟨i0, hi0⟩ := hS
    have := hS' i0 hi0
    rw [hw0, dotProduct_zero] at this
    exact Prod.ext haz (by simp only [Prod.snd_zero]; linarith)
  obtain ⟨⟨a, t⟩, h⟩ := (LinearMap.injective_iff_surjective.mp hinj) (0, 1)
  rw [hL] at h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only at h1 h2
  have hS' : ∀ i ∈ S, p i ⬝ᵥ (∑ k ∈ S, a k • p k) = -t := fun i hi ↦ by
    have := congrFun h1 i
    simp only [ite_eq_left hi, Pi.zero_apply] at this
    linarith
  have hout : ∀ i ∉ S, a i = 0 := fun i hi ↦ by
    have := congrFun h1 i
    simpa [hi] using this
  refine ⟨a, hout, h2, fun i hi ↦ ?_⟩
  have hww : (∑ k ∈ S, a k • p k) ⬝ᵥ (∑ k ∈ S, a k • p k) = -t := by
    rw [sum_smul_dotProduct (p := p) S a, sum_congr rfl fun i hi ↦ by rw [hS' i hi],
      ← sum_mul, h2, one_mul]
  simp only [gap, normSq, hww, hS' i hi, sub_self]

variable {p}

/-- The affine minimizer of a nonempty affinely independent support lies in `aff(S)`
and has zero gaps on `S`. -/
theorem affineMin_spec {S : Finset (Fin N)} (hS : S.Nonempty)
    (hAI : IsAffinelyIndependent p S) :
    affineMin p S ∈ affineHull p S ∧ ∀ i ∈ S, gap p i (affineMin p S) = 0 := by
  obtain ⟨lam, -, hsum, hgap⟩ := exists_gap_zero p hS hAI
  rw [affineMin_eq_of_gap_zero p ⟨lam, hsum, rfl⟩ hgap]
  exact ⟨⟨lam, hsum, rfl⟩, hgap⟩

/-- Pythagoras on `aff(S)` at a point with zero gaps on `S`. -/
theorem normSq_eq_of_gap_zero {S : Finset (Fin N)} {w : Fin D → ℝ}
    (hgap : ∀ i ∈ S, gap p i w = 0) {x : Fin D → ℝ} (hx : x ∈ affineHull p S) :
    normSq x = normSq w + normSq (x - w) := by
  obtain ⟨mu, hmu, rfl⟩ := hx
  rw [normSq_expand _ w, sub_dotProduct_eq_sum_gap p hmu,
    sum_eq_zero fun i hi ↦ by rw [hgap i hi, mul_zero]]
  ring

theorem isAffineMinimizerOf_affineMin {S : Finset (Fin N)} (hS : S.Nonempty)
    (hAI : IsAffinelyIndependent p S) : IsAffineMinimizerOf p S (affineMin p S) :=
  ⟨(affineMin_spec hS hAI).1, fun x hx ↦ by
    rw [normSq_eq_of_gap_zero (affineMin_spec hS hAI).2 hx]
    linarith [normSq_nonneg (x - affineMin p S)]⟩

theorem eq_affineMin_of_isAffineMinimizerOf {S : Finset (Fin N)} (hS : S.Nonempty)
    (hAI : IsAffinelyIndependent p S) {x : Fin D → ℝ} (hx : IsAffineMinimizerOf p S x) :
    x = affineMin p S := by
  have h1 := hx.2 _ (affineMin_spec hS hAI).1
  have h2 := normSq_eq_of_gap_zero (affineMin_spec hS hAI).2 hx.1
  have : normSq (x - affineMin p S) = 0 := le_antisymm (by linarith) (normSq_nonneg _)
  exact sub_eq_zero.mp (normSq_eq_zero.mp this)

/-- A point of `aff(S)` different from `w_S` is strictly longer. -/
theorem normSq_affineMin_lt {S : Finset (Fin N)} (hS : S.Nonempty)
    (hAI : IsAffinelyIndependent p S) {x : Fin D → ℝ} (hx : x ∈ affineHull p S)
    (hne : x ≠ affineMin p S) : normSq (affineMin p S) < normSq x := by
  rw [normSq_eq_of_gap_zero (affineMin_spec hS hAI).2 hx]
  have : normSq (x - affineMin p S) ≠ 0 := fun h ↦ hne (sub_eq_zero.mp (normSq_eq_zero.mp h))
  linarith [lt_of_le_of_ne (normSq_nonneg (x - affineMin p S)) (Ne.symm this)]

theorem isAffineCoeffsOf_affineCoeffs {S : Finset (Fin N)} (hS : S.Nonempty)
    (hAI : IsAffinelyIndependent p S) : IsAffineCoeffsOf p S (affineCoeffs p S) := by
  classical
  obtain ⟨lam, hsum, hw⟩ := (affineMin_spec hS hAI).1
  apply Classical.epsilon_spec (p := IsAffineCoeffsOf p S)
  refine ⟨fun i ↦ if i ∈ S then lam i else 0, fun i hi ↦ ite_eq_right hi, ?_, ?_⟩
  · rw [sum_congr rfl fun i hi ↦ ite_eq_left hi]
    exact hsum
  · rw [sum_congr rfl fun i hi ↦ show (if i ∈ S then lam i else 0) • p i = lam i • p i by
      rw [ite_eq_left hi]]
    exact hw.symm

/-- Lemma 1 (`lem:affine-min`)(b). -/
theorem affinelyIndependent_insert {S : Finset (Fin N)} (hS : S.Nonempty)
    (hAI : IsAffinelyIndependent p S) {j : Fin N} (hj : gap p j (affineMin p S) ≠ 0) :
    IsAffinelyIndependent p (insert j S) := by
  by_cases hjS : j ∈ S
  · rwa [insert_eq_of_mem hjS]
  intro β hβ hβs
  have hgap := (affineMin_spec hS hAI).2
  have key : ∑ i ∈ insert j S, β i * gap p i (affineMin p S) = 0 := by
    have := congrArg (· ⬝ᵥ affineMin p S) hβ
    simp only [sum_smul_dotProduct, zero_dotProduct] at this
    simp only [gap, mul_sub, sum_sub_distrib, this, ← sum_mul, hβs, zero_mul, sub_zero]
  rw [sum_insert hjS, sum_eq_zero fun i hi ↦ by rw [hgap i hi, mul_zero], add_zero] at key
  have hβj : β j = 0 := (mul_eq_zero.mp key).resolve_right hj
  rw [sum_insert hjS, hβj, zero_smul, zero_add] at hβ
  rw [sum_insert hjS, hβj, zero_add] at hβs
  intro i hi
  rcases mem_insert.mp hi with rfl | hi
  · exact hβj
  · exact hAI β hβ hβs i hi

/-- The affine minimizer of a corral lies in the convex hull of all atoms. -/
theorem affineMin_mem_convexHull {S : Finset (Fin N)} (hC : IsCorral p S) :
    affineMin p S ∈ convexHull p univ := by
  obtain ⟨hout, hsum, hcomb⟩ := isAffineCoeffsOf_affineCoeffs hC.1 hC.2.1
  refine ⟨affineCoeffs p S, fun i _ ↦ ?_, ?_, ?_⟩
  · by_cases hi : i ∈ S
    · exact (hC.2.2 i hi).le
    · rw [hout i hi]
  · rw [← sum_subset (subset_univ S) fun i _ hi ↦ hout i hi]
    exact hsum
  · rw [← sum_subset (subset_univ S) fun i _ hi ↦ by rw [hout i hi, zero_smul]]
    exact hcomb.symm

/-- Wolfe's criterion, the direction not in `WolfeFacts`: at the minimum-norm point,
no atom has negative gap. -/
theorem gap_nonneg_of_isMinNormPoint {w : Fin D → ℝ} (hw : IsMinNormPoint p w) (j : Fin N) :
    0 ≤ gap p j w := by
  classical
  by_contra hneg
  push Not at hneg
  obtain ⟨lam, hlam0, hlam1, hwl⟩ := hw.1
  set g := gap p j w with hg
  set c := normSq (p j - w) with hc
  have hc0 : 0 ≤ c := normSq_nonneg _
  have hcg : 0 < c - g := by linarith
  set t := -g / (c - g) with ht
  have ht0 : 0 < t := div_pos (by linarith) hcg
  have ht1 : t ≤ 1 := (div_le_one hcg).2 (by linarith)
  have htc : t * (c - g) = -g := div_mul_cancel₀ _ hcg.ne'
  have hx : w + t • (p j - w) ∈ convexHull p univ := by
    refine ⟨fun i ↦ (1 - t) * lam i + t * (if i = j then 1 else 0), fun i hi ↦ ?_, ?_, ?_⟩
    · have := hlam0 i hi
      have : 0 ≤ t * (if i = j then (1 : ℝ) else 0) := mul_nonneg ht0.le (by split_ifs <;> norm_num)
      nlinarith
    · simp only [sum_add_distrib, ← mul_sum, hlam1, sum_ite_eq', mem_univ, ite_true]
      ring
    · simp only [add_smul, mul_smul, sum_add_distrib, ← smul_sum, ← hwl, ite_smul, one_smul,
        zero_smul, sum_ite_eq', mem_univ, ite_true]
      module
  have hle := hw.2 _ hx
  have hexp : normSq (w + t • (p j - w)) = normSq w + 2 * t * g + t ^ 2 * c := by
    rw [normSq_expand (w + t • (p j - w)) w, add_sub_cancel_left]
    simp only [hc, hg, gap, normSq, smul_dotProduct, dotProduct_smul, sub_dotProduct,
      smul_eq_mul]
    ring
  rw [hexp] at hle
  have : t * g * (1 + t) < 0 := mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg ht0 hneg) (by linarith)
  nlinarith

/-- Lemma 1 (`lem:affine-min`) (all parts). -/
theorem affine_min_all (S : Finset (Fin N)) (hS : S.Nonempty)
    (hAI : IsAffinelyIndependent p S) :
    (IsAffineMinimizerOf p S (affineMin p S) ∧
      (∀ x, IsAffineMinimizerOf p S x → x = affineMin p S) ∧
      IsAffineCoeffsOf p S (affineCoeffs p S) ∧
      (∀ lam, IsAffineCoeffsOf p S lam → lam = affineCoeffs p S)) ∧
    (∀ w ∈ affineHull p S, w = affineMin p S ↔ ∀ i ∈ S, gap p i w = 0) ∧
    (∀ j, gap p j (affineMin p S) ≠ 0 → IsAffinelyIndependent p (insert j S)) ∧
    (IsCorral p S → (IsMinNormPoint p (affineMin p S) ↔ improving p (affineMin p S) = ∅)) := by
  refine ⟨⟨isAffineMinimizerOf_affineMin hS hAI,
    fun x hx ↦ eq_affineMin_of_isAffineMinimizerOf hS hAI hx,
    isAffineCoeffsOf_affineCoeffs hS hAI,
    fun lam h ↦ (affineCoeffs_eq_of p hAI h.1 h.2.1 h.2.2).symm⟩,
    fun w hw ↦ ⟨fun h ↦ h ▸ (affineMin_spec hS hAI).2,
      fun h ↦ (affineMin_eq_of_gap_zero p hw h).symm⟩,
    fun j hj ↦ affinelyIndependent_insert hS hAI hj, fun hC ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩⟩
  · rw [improving, filter_eq_empty_iff]
    exact fun j _ ↦ not_lt.mpr (gap_nonneg_of_isMinNormPoint h j)
  · rw [improving, filter_eq_empty_iff] at h
    exact isMinNormPoint_of_gap_nonneg p (affineMin_mem_convexHull hC)
      fun j ↦ not_lt.mp (h (mem_univ j))

/-! ### Well-definedness and termination -/

variable (p)

/-- Every singleton is a corral. -/
theorem isCorral_singleton (k : Fin N) : IsCorral p {k} := by
  classical
  have hAI : IsAffinelyIndependent p {k} := fun β _ hβs i hi ↦ by
    rw [mem_singleton.mp hi]
    simpa using hβs
  refine ⟨singleton_nonempty k, hAI, fun i hi ↦ ?_⟩
  rw [mem_singleton.mp hi]
  have hmin : affineMin p {k} = p k :=
    affineMin_eq_of_gap_zero p ⟨Pi.single k 1, by simp, by simp⟩ (by simp [gap, normSq])
  have h := affineCoeffs_eq_of p hAI (lam := Pi.single k 1)
    (fun i hi ↦ by simp [show i ≠ k from fun h ↦ hi (h ▸ mem_singleton_self i)])
    (by simp) (by simp [hmin])
  rw [h]
  simp

variable {p} in
/-- Subsets of affinely independent supports are affinely independent. -/
theorem IsAffinelyIndependent.mono {S T : Finset (Fin N)} (h : IsAffinelyIndependent p S)
    (hTS : T ⊆ S) : IsAffinelyIndependent p T := by
  classical
  intro β hβ hβs i hi
  let β' : Fin N → ℝ := fun k ↦ if k ∈ T then β k else 0
  have e1 : ∑ k ∈ S, β' k • p k = ∑ k ∈ T, β k • p k := by
    rw [← sum_subset hTS (fun k _ hk ↦ by simp [β', hk])]
    exact sum_congr rfl fun k hk ↦ by simp [β', hk]
  have e2 : ∑ k ∈ S, β' k = ∑ k ∈ T, β k := by
    rw [← sum_subset hTS (fun k _ hk ↦ by simp [β', hk])]
    exact sum_congr rfl fun k hk ↦ by simp [β', hk]
  have := h β' (e1.trans hβ) (e2.trans hβs) i (hTS hi)
  simpa [β', hi] using this

/-- An affinely independent support in `ℝ^D` has at most `D + 1` elements. -/
theorem card_le_of_affinelyIndependent {S : Finset (Fin N)} (hAI : IsAffinelyIndependent p S) :
    S.card ≤ D + 1 := by
  classical
  let L : (S → ℝ) →ₗ[ℝ] (Fin D → ℝ) × ℝ :=
    { toFun := fun β ↦ (∑ x : S, β x • p x, ∑ x : S, β x)
      map_add' := by intro a b; simp [add_smul, sum_add_distrib]
      map_smul' := by intro c a; simp [smul_sum, mul_smul, mul_sum] }
  have hinj : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    intro β hβ
    have h1 : ∑ x : S, β x • p x = 0 := congrArg Prod.fst hβ
    have h2 : ∑ x : S, β x = 0 := congrArg Prod.snd hβ
    let β' : Fin N → ℝ := fun i ↦ if h : i ∈ S then β ⟨i, h⟩ else 0
    have e1 : ∑ i ∈ S, β' i • p i = ∑ x : S, β x • p x := by
      rw [← sum_coe_sort S]
      exact sum_congr rfl fun x _ ↦ by simp [β', x.2]
    have e2 : ∑ i ∈ S, β' i = ∑ x : S, β x := by
      rw [← sum_coe_sort S]
      exact sum_congr rfl fun x _ ↦ by simp [β', x.2]
    have hz := hAI β' (e1.trans h1) (e2.trans h2)
    funext x
    have := hz x x.2
    simpa [β', x.2] using this
  have := LinearMap.finrank_le_finrank_of_injective hinj
  simpa [Module.finrank_prod, Module.finrank_fin_fun] using this

/-- Feasibility slightly to the right: if every coordinate is positive or nonnegative
and nondecreasing, a small positive step stays nonnegative. -/
theorem exists_pos_feasible (v d : Fin N → ℝ) (h : ∀ k, 0 < v k ∨ (0 ≤ v k ∧ 0 ≤ d k))
    {c : ℝ} (hc : 0 < c) : ∃ δ, 0 < δ ∧ δ ≤ c ∧ ∀ k, 0 ≤ v k + δ * d k := by
  have hev : ∀ k, ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 ≤ v k + δ * d k := by
    intro k
    rcases h k with hk | ⟨hv, hd⟩
    · have hcont : Continuous fun δ : ℝ ↦ v k + δ * d k := by fun_prop
      have := hcont.tendsto 0
      simp only [zero_mul, add_zero] at this
      exact nhdsWithin_le_nhds ((this.eventually (lt_mem_nhds hk)).mono fun _ h ↦ h.le)
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      have : (0 : ℝ) < δ := hδ
      exact add_nonneg hv (mul_nonneg this.le hd)
  obtain ⟨δ, h1, h2⟩ := ((Filter.eventually_all.2 hev).and (Ioo_mem_nhdsGT hc)).exists
  exact ⟨δ, h2.1, h2.2.le, h1⟩

/-- The step length is the maximum of the feasible step lengths. -/
theorem stepLength_spec {lam : Fin N → ℝ} (d : Fin N → ℝ) (hlam : ∀ k, 0 ≤ lam k) :
    0 ≤ stepLength lam d ∧ stepLength lam d ≤ 1 ∧
      (∀ k, 0 ≤ lam k + stepLength lam d * d k) ∧
      (∀ r, 0 ≤ r → r ≤ 1 → (∀ k, 0 ≤ lam k + r * d k) → r ≤ stepLength lam d) := by
  set F := {r : ℝ | 0 ≤ r ∧ r ≤ 1 ∧ ∀ k, 0 ≤ lam k + r * d k} with hF
  have h0 : (0 : ℝ) ∈ F := ⟨le_rfl, zero_le_one, fun k ↦ by simpa using hlam k⟩
  have hbdd : BddAbove F := ⟨1, fun r hr ↦ hr.2.1⟩
  have hcl : IsClosed F := by
    have : F = Set.Ici 0 ∩ Set.Iic 1 ∩ ⋂ k, {r | 0 ≤ lam k + r * d k} := by
      ext r
      simp [F, and_assoc]
    rw [this]
    exact (isClosed_Ici.inter isClosed_Iic).inter
      (isClosed_iInter fun k ↦ isClosed_le continuous_const (by fun_prop))
  have hmem : stepLength lam d ∈ F := hcl.csSup_mem ⟨0, h0⟩ hbdd
  exact ⟨hmem.1, hmem.2.1, hmem.2.2, fun r h0 h1 h2 ↦ le_csSup hbdd ⟨h0, h1, h2⟩⟩

/-- If the step length is `< 1`, some coordinate is blocking. -/
theorem stepLength_blocking {lam : Fin N → ℝ} (d : Fin N → ℝ) (hlam : ∀ k, 0 ≤ lam k)
    (ht : stepLength lam d < 1) : ∃ k, lam k + stepLength lam d * d k = 0 ∧ d k < 0 := by
  obtain ⟨-, -, hfeas, hmax⟩ := stepLength_spec d hlam
  set t := stepLength lam d
  by_contra hcon
  push Not at hcon
  have h : ∀ k, 0 < lam k + t * d k ∨ (0 ≤ lam k + t * d k ∧ 0 ≤ d k) := fun k ↦ by
    rcases (hfeas k).lt_or_eq with hk | hk
    · exact Or.inl hk
    · exact Or.inr ⟨hfeas k, hcon k hk.symm⟩
  obtain ⟨δ, hδ0, hδ1, hδ⟩ := exists_pos_feasible _ d h (sub_pos.2 ht)
  have := hmax (t + δ) (by linarith [(stepLength_spec d hlam).1]) (by linarith)
    (fun k ↦ by rw [add_mul]; linarith [hδ k])
  linarith

/-- `‖a + t(b - a)‖² ≤ (1-t)‖a‖² + t‖b‖²` for `t ∈ [0,1]`. -/
theorem normSq_segment_le {a b : Fin D → ℝ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    normSq (a + t • (b - a)) ≤ (1 - t) * normSq a + t * normSq b := by
  have h := mul_nonneg (mul_nonneg ht0 (sub_nonneg.2 ht1)) (normSq_nonneg (a - b))
  unfold normSq at *
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, sub_dotProduct,
    dotProduct_sub, smul_eq_mul, dotProduct_comm b a] at *
  nlinarith

/-- The states that Algorithm 2 (`alg:wolfe`) reaches inside a major cycle. -/
structure Good (s : State N) : Prop where
  ai : IsAffinelyIndependent p s.S
  nonneg : ∀ k, 0 ≤ s.lam k
  out : ∀ k ∉ s.S, s.lam k = 0
  sum : ∑ i ∈ s.S, s.lam i = 1

/-- The current point `∑_{i∈S} λ_i p_i` of a state. -/
def point (s : State N) : Fin D → ℝ := ∑ i ∈ s.S, s.lam i • p i

variable {p} in
theorem Good.nonempty {s : State N} (hg : Good p s) : s.S.Nonempty :=
  nonempty_of_sum_ne_zero (by rw [hg.sum]; exact one_ne_zero)

variable {p} in
theorem Good.point_mem {s : State N} (hg : Good p s) : point p s ∈ affineHull p s.S :=
  ⟨s.lam, hg.sum, rfl⟩

/-- A minor cycle from a good state leads to a good state; the current point moves
by the step length towards the affine minimizer of the current support. -/
theorem MinorCycle.good {s s' : State N} (hg : Good p s) (hm : MinorCycle p s s') :
    Good p s' ∧ point p s' = point p s +
      stepLength s.lam (affineCoeffs p s.S - s.lam) • (affineMin p s.S - point p s) := by
  classical
  obtain ⟨S', lam'⟩ := s'
  obtain ⟨-, hlam', i, hi, hi0, hS'⟩ := hm
  simp only at hlam' hi0 hS'
  subst hS' hlam'
  obtain ⟨hμout, hμsum, hμcomb⟩ := isAffineCoeffsOf_affineCoeffs hg.nonempty hg.ai
  set μ := affineCoeffs p s.S
  obtain ⟨-, -, hfeas, -⟩ := stepLength_spec (μ - s.lam) hg.nonneg
  set t := stepLength s.lam (μ - s.lam)
  have hval : ∀ k, (s.lam + t • (μ - s.lam)) k = s.lam k + t * (μ k - s.lam k) := fun k ↦ rfl
  have hsumS : ∑ k ∈ s.S, (s.lam + t • (μ - s.lam)) k = 1 := by
    simp only [hval, sum_add_distrib, ← mul_sum, sum_sub_distrib, hμsum, hg.sum]
    ring
  have hpt : ∑ k ∈ s.S, (s.lam + t • (μ - s.lam)) k • p k = point p s +
      t • (affineMin p s.S - point p s) := by
    simp only [hval, add_smul, mul_smul, sum_add_distrib, ← smul_sum, sub_smul,
      sum_sub_distrib, hμcomb, point]
  refine ⟨⟨hg.ai.mono (erase_subset i s.S), fun k ↦ hfeas k, fun k hk ↦ ?_, ?_⟩, ?_⟩
  · by_cases hki : k = i
    · rw [hki]
      exact hi0
    · have hkS : k ∉ s.S := fun h ↦ hk (mem_erase.mpr ⟨hki, h⟩)
      change (s.lam + t • (μ - s.lam)) k = 0
      rw [hval, hg.out k hkS, hμout k hkS]
      ring
  · simp only
    rw [sum_erase _ hi0]
    exact hsumS
  · simp only [point]
    rw [sum_erase _ (by rw [hi0, zero_smul])]
    exact hpt

/-- A minor cycle from a good state does not increase the norm of the current point,
and decreases it strictly if the step is positive and the affine minimizer of the
current support is shorter than the current point. -/
theorem MinorCycle.normSq_le {s s' : State N} (hg : Good p s) (hm : MinorCycle p s s') :
    normSq (point p s') ≤ normSq (point p s) ∧
      (0 < stepLength s.lam (affineCoeffs p s.S - s.lam) →
        normSq (affineMin p s.S) < normSq (point p s) →
        normSq (point p s') < normSq (point p s)) := by
  obtain ⟨-, hpt⟩ := hm.good p hg
  obtain ⟨ht0, ht1, -, -⟩ := stepLength_spec (affineCoeffs p s.S - s.lam) hg.nonneg
  set t := stepLength s.lam (affineCoeffs p s.S - s.lam)
  have hw := (isAffineMinimizerOf_affineMin hg.nonempty hg.ai).2 _ hg.point_mem
  have hseg := normSq_segment_le (a := point p s) (b := affineMin p s.S) ht0 ht1
  rw [← hpt] at hseg
  refine ⟨by nlinarith, fun htpos hlt ↦ by nlinarith⟩

/-- Along a chain of minor cycles from a good state, states stay good and the norm of the
current point does not increase. -/
theorem good_of_reflTransGen {s s' : State N} (hg : Good p s)
    (h : Relation.ReflTransGen (MinorCycle p) s s') :
    Good p s' ∧ normSq (point p s') ≤ normSq (point p s) := by
  induction h with
  | refl => exact ⟨hg, le_rfl⟩
  | tail _ hbc ih =>
    exact ⟨(hbc.good p ih.1).1, ((hbc.normSq_le p ih.1).1).trans ih.2⟩

/-- At a good state whose support is not a corral, a minor cycle can be performed. -/
theorem exists_minorCycle {s : State N} (hg : Good p s) (hnc : ¬ IsCorral p s.S) :
    ∃ s', MinorCycle p s s' := by
  classical
  obtain ⟨hμout, -, -⟩ := isAffineCoeffsOf_affineCoeffs hg.nonempty hg.ai
  set μ := affineCoeffs p s.S
  obtain ⟨-, ht1, hfeas, -⟩ := stepLength_spec (μ - s.lam) hg.nonneg
  set t := stepLength s.lam (μ - s.lam)
  have hval : ∀ k, (s.lam + t • (μ - s.lam)) k = s.lam k + t * (μ k - s.lam k) := fun k ↦ rfl
  suffices h : ∃ i ∈ s.S, (s.lam + t • (μ - s.lam)) i = 0 by
    obtain ⟨i, hi, h0⟩ := h
    exact ⟨⟨s.S.erase i, s.lam + t • (μ - s.lam)⟩, hnc, rfl, i, hi, h0, rfl⟩
  rcases ht1.lt_or_eq with ht | ht
  · obtain ⟨k, hk0, hkd⟩ := stepLength_blocking (μ - s.lam) hg.nonneg ht
    refine ⟨k, ?_, by rw [hval]; exact hk0⟩
    by_contra hkS
    simp only [Pi.sub_apply, hμout k hkS, hg.out k hkS, sub_self] at hkd
    exact lt_irrefl _ hkd
  · have : ∃ i ∈ s.S, μ i ≤ 0 := by
      by_contra hcon
      push Not at hcon
      exact hnc ⟨hg.nonempty, hg.ai, hcon⟩
    obtain ⟨i, hi, hμi⟩ := this
    refine ⟨i, hi, ?_⟩
    have := hfeas i
    rw [ht] at this
    rw [hval, ht]
    simp only [Pi.sub_apply, one_mul] at this ⊢
    linarith

/-- From a good state, a chain of minor cycles reaches a corral. -/
theorem exists_corral_of_good (s : State N) (hg : Good p s) :
    ∃ s', Relation.ReflTransGen (MinorCycle p) s s' ∧ IsCorral p s'.S := by
  induction hn : s.S.card using Nat.strong_induction_on generalizing s with
  | _ n ih =>
    by_cases hc : IsCorral p s.S
    · exact ⟨s, Relation.ReflTransGen.refl, hc⟩
    obtain ⟨s', hm⟩ := exists_minorCycle p hg hc
    obtain ⟨-, -, i, hi, -, hS'⟩ := id hm
    have hcard : s'.S.card < n := by
      rw [hS', card_erase_of_mem hi, ← hn]
      exact Nat.sub_lt (card_pos.mpr ⟨i, hi⟩) one_pos
    obtain ⟨s'', h1, h2⟩ := ih _ hcard s' ((hm.good p hg).1) rfl
    exact ⟨s'', Relation.ReflTransGen.head hm h1, h2⟩

/-- An improving atom is not in the corral. -/
theorem not_mem_of_improving {S : Finset (Fin N)} (hC : IsCorral p S) {j : Fin N}
    (hj : j ∈ improving p (affineMin p S)) : j ∉ S := fun h ↦ by
  have h1 := (affineMin_spec hC.1 hC.2.1).2 j h
  have h2 : gap p j (affineMin p S) < 0 := (mem_filter.mp hj).2
  linarith

/-- The start state of a major cycle is good, and its current point is `w_S`. -/
theorem good_start {S : Finset (Fin N)} (hC : IsCorral p S) {j : Fin N}
    (hj : j ∈ improving p (affineMin p S)) :
    Good p ⟨insert j S, affineCoeffs p S⟩ ∧
      point p ⟨insert j S, affineCoeffs p S⟩ = affineMin p S := by
  have hjS := not_mem_of_improving p hC hj
  have hgap : gap p j (affineMin p S) < 0 := (mem_filter.mp hj).2
  obtain ⟨hout, hsum, hcomb⟩ := isAffineCoeffsOf_affineCoeffs hC.1 hC.2.1
  refine ⟨⟨affinelyIndependent_insert hC.1 hC.2.1 hgap.ne, fun k ↦ ?_,
    fun k hk ↦ hout k fun h ↦ hk (mem_insert_of_mem h), ?_⟩, ?_⟩
  · change 0 ≤ affineCoeffs p S k
    by_cases hk : k ∈ S
    · exact (hC.2.2 k hk).le
    · rw [hout k hk]
  · simp only
    rw [sum_insert hjS, hout j hjS, zero_add, hsum]
  · simp only [point]
    rw [sum_insert hjS, hout j hjS, zero_smul, zero_add, hcomb]

/-- In a major cycle at the corral `S` inserting `j`, the coefficient of `j` in the
affine minimizer of `S ∪ {j}` is positive, and that affine minimizer is shorter than
`w_S`. -/
theorem insert_facts {S : Finset (Fin N)} (hC : IsCorral p S) {j : Fin N}
    (hj : j ∈ improving p (affineMin p S)) :
    normSq (affineMin p (insert j S)) < normSq (affineMin p S) ∧
      0 < affineCoeffs p (insert j S) j := by
  have hjS := not_mem_of_improving p hC hj
  have hgap : gap p j (affineMin p S) < 0 := (mem_filter.mp hj).2
  obtain ⟨hg0, hpt0⟩ := good_start p hC hj
  set T := insert j S
  have hTne : T.Nonempty := insert_nonempty j S
  have hTAI : IsAffinelyIndependent p T := hg0.ai
  have hwT : affineMin p S ∈ affineHull p T := hpt0 ▸ hg0.point_mem
  have hne : affineMin p S ≠ affineMin p T := fun h ↦ by
    have := (affineMin_spec hTne hTAI).2 j (mem_insert_self j S)
    rw [← h] at this
    linarith
  have hlt := normSq_affineMin_lt hTne hTAI hwT hne
  refine ⟨hlt, ?_⟩
  -- the two identities of the paper
  obtain ⟨-, hsumS, hcombS⟩ := isAffineCoeffsOf_affineCoeffs hC.1 hC.2.1
  obtain ⟨-, hsumT, hcombT⟩ := isAffineCoeffsOf_affineCoeffs hTne hTAI
  have hgapT := (affineMin_spec hTne hTAI).2
  have hgapS := (affineMin_spec hC.1 hC.2.1).2
  have e1 : (affineMin p S - affineMin p T) ⬝ᵥ affineMin p T = 0 := by
    rw [← hcombS, sub_dotProduct_eq_sum_gap p hsumS]
    exact sum_eq_zero fun i hi ↦ by rw [hgapT i (mem_insert_of_mem hi), mul_zero]
  have e2 : (affineMin p T - affineMin p S) ⬝ᵥ affineMin p S =
      affineCoeffs p T j * gap p j (affineMin p S) := by
    rw [← hcombT, sub_dotProduct_eq_sum_gap p hsumT, sum_insert hjS,
      sum_eq_zero fun i hi ↦ by rw [hgapS i hi, mul_zero], add_zero]
  have e3 : normSq (affineMin p T) = normSq (affineMin p S) +
      affineCoeffs p T j * gap p j (affineMin p S) := by
    simp only [sub_dotProduct, dotProduct_comm (affineMin p T) (affineMin p S)] at e1 e2
    unfold normSq
    linarith
  by_contra hcon
  push Not at hcon
  nlinarith

/-- Every major cycle strictly decreases the norm of the affine minimizer. -/
theorem MajorCycle.normSq_lt {S S' : Finset (Fin N)} {j : Fin N} (hM : MajorCycle p S j S') :
    normSq (affineMin p S') < normSq (affineMin p S) := by
  obtain ⟨hC, hj, lam', hrt, hC'⟩ := hM
  obtain ⟨hg0, hpt0⟩ := good_start p hC hj
  obtain ⟨hltT, hμj⟩ := insert_facts p hC hj
  obtain ⟨hgf, -⟩ := good_of_reflTransGen p hg0 hrt
  have hfin : normSq (affineMin p S') ≤ normSq (point p ⟨S', lam'⟩) :=
    (isAffineMinimizerOf_affineMin hC'.1 hC'.2.1).2 _ hgf.point_mem
  rcases hrt.cases_head with h | ⟨c, hm, hrt'⟩
  · have : S' = insert j S := (congrArg State.S h).symm
    rw [this]
    exact hltT
  · -- the first minor cycle has a positive step
    classical
    set lam0 := affineCoeffs p S
    set μ := affineCoeffs p (insert j S)
    obtain ⟨hμout, -, -⟩ := isAffineCoeffsOf_affineCoeffs (insert_nonempty j S) hg0.ai
    have hjS := not_mem_of_improving p hC hj
    have hpos : 0 < stepLength lam0 (μ - lam0) := by
      have h : ∀ k, 0 < lam0 k ∨ (0 ≤ lam0 k ∧ 0 ≤ (μ - lam0) k) := fun k ↦ by
        by_cases hkS : k ∈ S
        · exact Or.inl (hC.2.2 k hkS)
        · right
          refine ⟨hg0.nonneg k, ?_⟩
          simp only [Pi.sub_apply]
          have hl : lam0 k = 0 := (isAffineCoeffsOf_affineCoeffs hC.1 hC.2.1).1 k hkS
          rw [hl, sub_zero]
          by_cases hkj : k = j
          · rw [hkj]; exact hμj.le
          · rw [show μ k = 0 from hμout k (by simp [hkj, hkS])]
      obtain ⟨δ, hδ0, hδ1, hδ⟩ := exists_pos_feasible lam0 (μ - lam0) h one_pos
      exact hδ0.trans_le ((stepLength_spec (μ - lam0) hg0.nonneg).2.2.2 δ hδ0.le hδ1 hδ)
    have hstrict := (hm.normSq_le p hg0).2 hpos (by rw [hpt0]; exact hltT)
    have hgc := (hm.good p hg0).1
    have hle := (good_of_reflTransGen p hgc hrt').2
    rw [hpt0] at hstrict
    linarith

/-- Well-definedness and termination of Wolfe's method. -/
theorem wolfe_well_defined_all :
    (∀ k, IsCorral p {k}) ∧
    (∀ S j, IsCorral p S → j ∈ improving p (affineMin p S) → ∃ S', MajorCycle p S j S') ∧
    (∀ S j s, IsCorral p S → j ∈ improving p (affineMin p S) →
      Relation.ReflTransGen (MinorCycle p) ⟨insert j S, affineCoeffs p S⟩ s →
      IsAffinelyIndependent p s.S ∧ (∀ k, 0 ≤ s.lam k) ∧
      (¬ IsCorral p s.S → ∃ s', MinorCycle p s s')) ∧
    (∀ S j (k : ℕ) (s : ℕ → Wolfe.State N), IsCorral p S → j ∈ improving p (affineMin p S) →
      s 0 = ⟨insert j S, affineCoeffs p S⟩ → (∀ t < k, MinorCycle p (s t) (s (t + 1))) →
      k ≤ D) ∧
    (∀ S j S', MajorCycle p S j S' → normSq (affineMin p S') < normSq (affineMin p S)) ∧
    ∀ (ch : Finset (Fin N) → Fin N → Prop) f S, IsPartialWolfeRunWith p ch f S →
      Set.InjOn S (Set.Iic f) ∧ f < 2 ^ N := by
  refine ⟨isCorral_singleton p, fun S j hC hj ↦ ?_, fun S j s hC hj hrt ↦ ?_,
    fun S j k s hC hj h0 hmin ↦ ?_,
    fun S j S' hM ↦ hM.normSq_lt p, fun ch f S hrun ↦ ?_⟩
  · obtain ⟨s', hrt, hc⟩ := exists_corral_of_good p _ (good_start p hC hj).1
    exact ⟨s'.S, hC, hj, s'.lam, hrt, hc⟩
  · have hg := (good_of_reflTransGen p (good_start p hC hj).1 hrt).1
    exact ⟨hg.ai, hg.nonneg, fun hnc ↦ exists_minorCycle p hg hnc⟩
  · have hcard : ∀ t ≤ k, (s t).S.card + t = (insert j S).card := by
      intro t
      induction t with
      | zero => intro _; simp [h0]
      | succ t ih =>
        intro ht
        obtain ⟨-, -, i, hi, -, hS'⟩ := hmin t (by omega)
        rw [hS', card_erase_of_mem hi]
        have := ih (by omega)
        have := card_pos.2 ⟨i, hi⟩
        omega
    have hS : (insert j S).card ≤ D + 1 :=
      card_le_of_affinelyIndependent p (good_start p hC hj).1.ai
    rcases k with _ | k
    · omega
    obtain ⟨hnc, -, i, hi, -, -⟩ := hmin k (by omega)
    have h2 : 2 ≤ (s k).S.card := by
      by_contra hlt
      push Not at hlt
      have h1 : (s k).S.card = 1 := le_antisymm (by omega) (card_pos.2 ⟨i, hi⟩)
      obtain ⟨a, ha⟩ := card_eq_one.mp h1
      exact hnc (ha ▸ isCorral_singleton p a)
    have := hcard k (by omega)
    omega
  · obtain ⟨-, hstep⟩ := hrun
    have hdec : ∀ a c, a + c + 1 ≤ f →
        normSq (affineMin p (S (a + c + 1))) < normSq (affineMin p (S a)) := by
      intro a c
      induction c with
      | zero =>
        intro h
        obtain ⟨j, -, hM⟩ := hstep a (by omega)
        exact hM.normSq_lt p
      | succ c ih =>
        intro h
        obtain ⟨j, -, hM⟩ := hstep (a + c + 1) (by omega)
        exact (hM.normSq_lt p).trans (ih (by omega))
    have hinj : Set.InjOn S (Set.Iic f) := by
      intro a ha b hb hab
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_lt h
        have := hdec a c hb
        rw [hab] at this
        exact lt_irrefl _ this
      · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_lt h
        have := hdec b c ha
        rw [hab] at this
        exact lt_irrefl _ this
    refine ⟨hinj, ?_⟩
    let g : Fin (f + 1) → Finset (Fin N) := fun i ↦ S i
    have hg : Function.Injective g := fun a b hab ↦
      Fin.ext (hinj (Set.mem_Iic.mpr (Nat.lt_succ_iff.mp a.2))
        (Set.mem_Iic.mpr (Nat.lt_succ_iff.mp b.2)) hab)
    have := Fintype.card_le_of_injective g hg
    simp only [Fintype.card_fin, Fintype.card_finset] at this
    omega

end Wolfe

open Finset Wolfe

/-- Lemma 1 (`lem:affine-min`), together with the well-definedness of `w_S` and `λ^{*S}`
(statement copied verbatim from `MainResults.affine_min`). -/
theorem affine_min_main {N D : ℕ} (p : Fin N → Fin D → ℝ) (S : Finset (Fin N)) (hS : S.Nonempty)
    (hAI : IsAffinelyIndependent p S) :
    (IsAffineMinimizerOf p S (affineMin p S) ∧
      (∀ x, IsAffineMinimizerOf p S x → x = affineMin p S) ∧
      IsAffineCoeffsOf p S (affineCoeffs p S) ∧
      (∀ lam, IsAffineCoeffsOf p S lam → lam = affineCoeffs p S)) ∧
    (∀ w ∈ affineHull p S, w = affineMin p S ↔ ∀ i ∈ S, gap p i w = 0) ∧
    (∀ j, gap p j (affineMin p S) ≠ 0 → IsAffinelyIndependent p (insert j S)) ∧
    (IsCorral p S → (IsMinNormPoint p (affineMin p S) ↔ improving p (affineMin p S) = ∅)) :=
  affine_min_all S hS hAI

/-- Well-definedness and termination of Wolfe's method
(statement copied verbatim from `MainResults.wolfe_well_defined`). -/
theorem wolfe_well_defined_main {N D : ℕ} (p : Fin N → Fin D → ℝ) :
    (∀ k, IsCorral p {k}) ∧
    (∀ S j, IsCorral p S → j ∈ improving p (affineMin p S) → ∃ S', MajorCycle p S j S') ∧
    (∀ S j s, IsCorral p S → j ∈ improving p (affineMin p S) →
      Relation.ReflTransGen (MinorCycle p) ⟨insert j S, affineCoeffs p S⟩ s →
      IsAffinelyIndependent p s.S ∧ (∀ k, 0 ≤ s.lam k) ∧
      (¬ IsCorral p s.S → ∃ s', MinorCycle p s s')) ∧
    (∀ S j (k : ℕ) (s : ℕ → Wolfe.State N), IsCorral p S → j ∈ improving p (affineMin p S) →
      s 0 = ⟨insert j S, affineCoeffs p S⟩ → (∀ t < k, MinorCycle p (s t) (s (t + 1))) →
      k ≤ D) ∧
    (∀ S j S', MajorCycle p S j S' → normSq (affineMin p S') < normSq (affineMin p S)) ∧
    ∀ (ch : Finset (Fin N) → Fin N → Prop) f S, IsPartialWolfeRunWith p ch f S →
      Set.InjOn S (Set.Iic f) ∧ f < 2 ^ N :=
  wolfe_well_defined_all p

end WolfeSimplex
