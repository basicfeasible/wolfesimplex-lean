import WolfeSimplex.Defs.Shield
import WolfeSimplex.Proofs.Hat

/-!
# The canonical LP and the shield (paper: Lemma 12 (`lem:shield-lp`), Lemma 16 (`lem:weighted`)(a))

## Proof structure

First, a general part about real LPs `L'` with `m + 1` rows and `n + 1` labels that
arise from an LP `L` (with `m` rows and `n` labels) in the "shield shape" (`IsShieldOf`):

* row `i.castSucc` of `L'` is row `i` of `G A` (with an injective matrix `G`), where
  the column of label `k` is multiplied by `s k > 0`; the shield `ω = Fin.last n` has
  the entry `0` there, and the right-hand side is `2 (G b)_i`;
* the last row is `dω x_ω - ∑_k a_k x_k = 1` with `dω > 0`, `a_k ≥ 0`;
* the costs are `s_k (κ c_k - uᵀ A_k)` and `0` for `ω`.

For such `L'`, the map `x ↦ φ(x) = (2 x_k / s_k, (1 + ∑_k a_k 2 x_k / s_k) / dω)`
maps the solutions of `A x = b` bijectively onto those of `A' z = b'`, and everything
in Lemma 12 (`lem:shield-lp`) follows (as in the paper). Both (LP⁺) (`s = 1`) and (LP̃⁺)
(`s_ℓ = d_ℓ / Δ₀` for `ℓ ∈ B₀`, `s_k = 1` otherwise) have this shape, with `κ = Δ₀`.
-/

namespace WolfeSimplex

open Finset Matrix

namespace LP

variable {m n : ℕ}

/-- Basic directions are unique (for a basis). -/
theorem IsBasis.eq_basicDir {P : LP m n} {B : Finset (Fin n)} (hB : P.IsBasis B) {j : Fin n}
    (hj : j ∉ B) {d : Fin n → ℝ} (hd : P.IsBasicDirOf B j d) : d = P.basicDir B j := by
  obtain ⟨h1, h2, h3⟩ := hB.basicDir_spec hj
  obtain ⟨g1, g2, g3⟩ := hd
  have key := hB.eq_zero (x := d - P.basicDir B j) (fun k hk ↦ ?_)
    (by rw [mulVec_sub, h1, g1, sub_self])
  · exact sub_eq_zero.1 key
  · by_cases hkj : k = j
    · subst hkj; simp [h2, g2]
    · simp [h3 k hk hkj, g3 k hk hkj]

/-- The "shield shape" of an LP `L'` built from `L` (see the module docstring). -/
structure IsShieldOf (L : LP m n) (L' : LP (m + 1) (n + 1)) (G : Matrix (Fin m) (Fin m) ℝ)
    (s : Fin n → ℝ) (κ : ℝ) (u : Fin m → ℝ) (a : Fin n → ℝ) (dω : ℝ) : Prop where
  G_inj : ∀ v, G *ᵥ v = 0 → v = 0
  s_pos : ∀ k, 0 < s k
  a_nonneg : ∀ k, 0 ≤ a k
  dω_pos : 0 < dω
  A_cc : ∀ (i : Fin m) (k : Fin n), L'.A i.castSucc k.castSucc = s k * (G * L.A) i k
  A_cl : ∀ i : Fin m, L'.A i.castSucc (Fin.last n) = 0
  A_lc : ∀ k : Fin n, L'.A (Fin.last m) k.castSucc = -a k
  A_ll : L'.A (Fin.last m) (Fin.last n) = dω
  b_c : ∀ i : Fin m, L'.b i.castSucc = 2 * (G *ᵥ L.b) i
  b_l : L'.b (Fin.last m) = 1
  c_c : ∀ k : Fin n, L'.c k.castSucc = s k * (κ * L.c k - u ⬝ᵥ L.col k)
  c_l : L'.c (Fin.last n) = 0

/-- `π(z)_k = s_k z_k / 2`: the point of `L` belonging to the point `z` of `L'`. -/
noncomputable def shieldPr (s : Fin n → ℝ) (z : Fin (n + 1) → ℝ) : Fin n → ℝ :=
  fun k ↦ s k * z k.castSucc / 2

/-- The left-hand side `dω z_ω - ∑_k a_k z_k` of the shield row. -/
noncomputable def shieldRow (a : Fin n → ℝ) (dω : ℝ) (z : Fin (n + 1) → ℝ) : ℝ :=
  dω * z (Fin.last n) - ∑ k, a k * z k.castSucc

/-- `φ_t(x) = (2 x_k / s_k, (t + ∑_k a_k 2 x_k / s_k) / dω)`. -/
noncomputable def shieldLift (s a : Fin n → ℝ) (dω t : ℝ) (x : Fin n → ℝ) :
    Fin (n + 1) → ℝ :=
  Fin.snoc (α := fun _ ↦ ℝ) (fun k ↦ 2 * x k / s k) ((t + ∑ k, a k * (2 * x k / s k)) / dω)

@[simp] theorem shieldLift_castSucc (s a : Fin n → ℝ) (dω t : ℝ) (x : Fin n → ℝ) (k : Fin n) :
    shieldLift s a dω t x k.castSucc = 2 * x k / s k := by
  simp [shieldLift]

@[simp] theorem shieldLift_last (s a : Fin n → ℝ) (dω t : ℝ) (x : Fin n → ℝ) :
    shieldLift s a dω t x (Fin.last n) = (t + ∑ k, a k * (2 * x k / s k)) / dω := by
  simp [shieldLift]

theorem shieldPr_add_smul (s : Fin n → ℝ) (z w : Fin (n + 1) → ℝ) (r : ℝ) :
    shieldPr s (z + r • w) = shieldPr s z + r • shieldPr s w := by
  funext k; simp [shieldPr]; ring

theorem shieldRow_add_smul (a : Fin n → ℝ) (dω : ℝ) (z w : Fin (n + 1) → ℝ) (r : ℝ) :
    shieldRow a dω (z + r • w) = shieldRow a dω z + r * shieldRow a dω w := by
  simp only [shieldRow, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
  have : ∑ k, a k * (r * w k.castSucc) = r * ∑ k, a k * w k.castSucc := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ ↦ by ring
  rw [this]; ring

namespace IsShieldOf

variable {L : LP m n} {L' : LP (m + 1) (n + 1)} {G : Matrix (Fin m) (Fin m) ℝ}
  {s : Fin n → ℝ} {κ : ℝ} {u : Fin m → ℝ} {a : Fin n → ℝ} {dω : ℝ}
  (h : L.IsShieldOf L' G s κ u a dω)
include h

theorem pr_lift (t : ℝ) (x : Fin n → ℝ) : shieldPr s (shieldLift s a dω t x) = x := by
  funext k
  have := (h.s_pos k).ne'
  simp only [shieldPr, shieldLift_castSucc]
  field_simp

theorem row_lift (t : ℝ) (x : Fin n → ℝ) : shieldRow a dω (shieldLift s a dω t x) = t := by
  have := h.dω_pos.ne'
  simp only [shieldRow, shieldLift_castSucc, shieldLift_last]
  rw [mul_div_cancel₀ _ this]; ring

theorem eq_lift (z : Fin (n + 1) → ℝ) :
    z = shieldLift s a dω (shieldRow a dω z) (shieldPr s z) := by
  have hk : ∀ k, 2 * (s k * z k.castSucc / 2) / s k = z k.castSucc := fun k ↦ by
    have := (h.s_pos k).ne'
    field_simp
  funext ℓ
  induction ℓ using Fin.lastCases with
  | last =>
    have := h.dω_pos.ne'
    simp only [shieldLift_last, shieldPr, hk, shieldRow]
    field_simp; ring
  | cast k => simp [shieldPr, hk]

theorem mulVec_castSucc (z : Fin (n + 1) → ℝ) (i : Fin m) :
    (L'.A *ᵥ z) i.castSucc = 2 * (G *ᵥ (L.A *ᵥ shieldPr s z)) i := by
  rw [mulVec_mulVec]
  simp only [mulVec, dotProduct, Fin.sum_univ_castSucc, h.A_cc, h.A_cl, zero_mul, add_zero,
    shieldPr, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ ↦ by ring

theorem mulVec_last (z : Fin (n + 1) → ℝ) :
    (L'.A *ᵥ z) (Fin.last m) = shieldRow a dω z := by
  simp only [mulVec, dotProduct, Fin.sum_univ_castSucc, h.A_lc, h.A_ll, shieldRow, neg_mul,
    Finset.sum_neg_distrib]
  ring

theorem mulVec_eq_b_iff (z : Fin (n + 1) → ℝ) :
    L'.A *ᵥ z = L'.b ↔ L.A *ᵥ shieldPr s z = L.b ∧ shieldRow a dω z = 1 := by
  rw [funext_iff, Fin.forall_fin_succ']
  simp only [h.mulVec_castSucc, h.mulVec_last, h.b_c, h.b_l]
  refine and_congr_left' ⟨fun H ↦ ?_, fun H i ↦ by rw [H]⟩
  have : G *ᵥ (L.A *ᵥ shieldPr s z - L.b) = 0 := by
    funext i; simp only [mulVec_sub, Pi.sub_apply, Pi.zero_apply]; linarith [H i]
  exact sub_eq_zero.1 (h.G_inj _ this)

theorem mulVec_eq_zero_iff (z : Fin (n + 1) → ℝ) :
    L'.A *ᵥ z = 0 ↔ L.A *ᵥ shieldPr s z = 0 ∧ shieldRow a dω z = 0 := by
  rw [funext_iff, Fin.forall_fin_succ']
  simp only [h.mulVec_castSucc, h.mulVec_last, Pi.zero_apply]
  refine and_congr_left' ⟨fun H ↦ ?_, fun H i ↦ by simp [H]⟩
  have : G *ᵥ (L.A *ᵥ shieldPr s z) = 0 := by
    funext i; simp only [Pi.zero_apply]; linarith [H i]
  exact h.G_inj _ this

theorem lift_eq_b_iff (x : Fin n → ℝ) :
    L'.A *ᵥ shieldLift s a dω 1 x = L'.b ↔ L.A *ᵥ x = L.b := by
  rw [h.mulVec_eq_b_iff, h.pr_lift, h.row_lift]; simp

theorem lift_nonneg {x : Fin n → ℝ} (hx : ∀ k, 0 ≤ x k) {t : ℝ} (ht : 0 ≤ t) :
    ∀ ℓ, 0 ≤ shieldLift s a dω t x ℓ := by
  have hs := h.s_pos
  intro ℓ
  induction ℓ using Fin.lastCases with
  | last =>
    rw [shieldLift_last]
    refine div_nonneg (add_nonneg ht (Finset.sum_nonneg fun k _ ↦ ?_)) h.dω_pos.le
    exact mul_nonneg (h.a_nonneg k) (div_nonneg (by linarith [hx k]) (hs k).le)
  | cast k =>
    rw [shieldLift_castSucc]
    exact div_nonneg (by linarith [hx k]) (hs k).le

theorem lift_last_pos {x : Fin n → ℝ} (hx : ∀ k, 0 ≤ x k) :
    0 < shieldLift s a dω 1 x (Fin.last n) := by
  have hs := h.s_pos
  rw [shieldLift_last]
  refine div_pos (add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun k _ ↦ ?_)) h.dω_pos
  exact mul_nonneg (h.a_nonneg k) (div_nonneg (by linarith [hx k]) (hs k).le)

theorem nonneg_of_lift {x : Fin n → ℝ} {t : ℝ} (hx : ∀ ℓ, 0 ≤ shieldLift s a dω t x ℓ) :
    ∀ k, 0 ≤ x k := by
  intro k
  have h1 := hx k.castSucc
  rw [shieldLift_castSucc] at h1
  have h2 := h.s_pos k
  have : 0 ≤ 2 * x k := by
    have := mul_nonneg h1 h2.le
    rwa [div_mul_cancel₀ _ h2.ne'] at this
  linarith

/-- `B ∪ {ω}` is a basis of `L'` if `B` is a basis of `L`. -/
theorem isBasis_hat {B : Finset (Fin n)} (hB : L.IsBasis B) : L'.IsBasis (hat B) := by
  refine ⟨by rw [IntLP.card_hat, hB.1], ?_⟩
  rw [linIndep_iff]
  intro z hz hAz
  rw [h.mulVec_eq_zero_iff] at hAz
  have hpr : shieldPr s z = 0 := hB.eq_zero (fun k hk ↦ by
    simp [shieldPr, hz k.castSucc (by simpa using hk)]) hAz.1
  rw [h.eq_lift z, hpr, hAz.2]
  funext ℓ
  induction ℓ using Fin.lastCases with
  | last => simp
  | cast k => simp

/-- `B` is a basis of `L` if `B ∪ {ω}` is a basis of `L'`. -/
theorem isBasis_of_hat {B : Finset (Fin n)} (hB : L'.IsBasis (hat B)) : L.IsBasis B := by
  refine ⟨by have := hB.1; rw [IntLP.card_hat] at this; omega, ?_⟩
  rw [linIndep_iff]
  intro x hx hAx
  have hz : ∀ ℓ ∉ hat B, shieldLift s a dω 0 x ℓ = 0 := by
    intro ℓ hℓ
    induction ℓ using Fin.lastCases with
    | last => exact absurd IntLP.last_mem_hat hℓ
    | cast k => simp [hx k (by simpa using hℓ)]
  have h0 := hB.eq_zero hz (by rw [h.mulVec_eq_zero_iff, h.pr_lift, h.row_lift]; exact ⟨hAx, rfl⟩)
  rw [← h.pr_lift 0 x, h0]
  funext k; simp [shieldPr]

theorem basicSol_hat {B : Finset (Fin n)} (hB : L.IsBasis B) :
    L'.basicSol (hat B) = shieldLift s a dω 1 (L.basicSol B) := by
  refine ((h.isBasis_hat hB).eq_basicSol ((h.lift_eq_b_iff _).2 hB.basicSol_spec.1) ?_).symm
  intro ℓ hℓ
  induction ℓ using Fin.lastCases with
  | last => exact absurd IntLP.last_mem_hat hℓ
  | cast k => simp [hB.basicSol_spec.2 k (by simpa using hℓ)]

theorem isFeasibleBasis_hat_iff (B : Finset (Fin n)) :
    L'.IsFeasibleBasis (hat B) ↔ L.IsFeasibleBasis B := by
  constructor
  · intro hB'
    have hB := h.isBasis_of_hat hB'.1
    refine ⟨hB, h.nonneg_of_lift (t := 1) ?_⟩
    rw [← h.basicSol_hat hB]; exact hB'.2
  · intro hB
    refine ⟨h.isBasis_hat hB.1, ?_⟩
    rw [h.basicSol_hat hB.1]
    exact h.lift_nonneg hB.2 zero_le_one

omit h in
theorem eq_hat_of_last_mem {B' : Finset (Fin (n + 1))} (hω : Fin.last n ∈ B') :
    B' = hat (univ.filter fun k ↦ k.castSucc ∈ B') := by
  ext ℓ
  induction ℓ using Fin.lastCases with
  | last => simp [hω, IntLP.last_mem_hat]
  | cast k => simp

theorem isFeasibleBasis_iff (B' : Finset (Fin (n + 1))) :
    L'.IsFeasibleBasis B' ↔ ∃ B, L.IsFeasibleBasis B ∧ B' = hat B := by
  constructor
  · intro hB'
    set z := L'.basicSol B'
    obtain ⟨hAz, hz0⟩ := hB'.1.basicSol_spec
    rw [h.mulVec_eq_b_iff] at hAz
    have hzeq := h.eq_lift z
    rw [hAz.2] at hzeq
    have hpr : ∀ k, 0 ≤ shieldPr s z k := h.nonneg_of_lift (t := 1) (hzeq ▸ hB'.2)
    have hpos : 0 < z (Fin.last n) := by rw [hzeq]; exact h.lift_last_pos hpr
    have hω : Fin.last n ∈ B' := by
      by_contra hω
      have : z (Fin.last n) = 0 := hz0 _ hω
      linarith
    have heq := IsShieldOf.eq_hat_of_last_mem hω
    refine ⟨_, ?_, heq⟩
    rw [← h.isFeasibleBasis_hat_iff, ← heq]; exact hB'
  · rintro ⟨B, hB, rfl⟩
    exact (h.isFeasibleBasis_hat_iff B).2 hB

theorem feasibleSetNonemptyBounded (hL : L.FeasibleSetNonemptyBounded) :
    L'.FeasibleSetNonemptyBounded := by
  obtain ⟨⟨x₀, hx₀⟩, R, hR⟩ := hL
  have hs := h.s_pos
  refine ⟨⟨shieldLift s a dω 1 x₀, (h.lift_eq_b_iff x₀).2 hx₀.1,
    h.lift_nonneg hx₀.2 zero_le_one⟩, ?_⟩
  set R₁ : ℝ := ∑ k, 2 * |R| / s k
  set R₂ : ℝ := (1 + ∑ k, a k * (2 * |R| / s k)) / dω
  have hR₁ : 0 ≤ R₁ := Finset.sum_nonneg fun k _ ↦ div_nonneg (by positivity) (hs k).le
  have hR₂ : 0 ≤ R₂ := div_nonneg (add_nonneg zero_le_one (Finset.sum_nonneg fun k _ ↦
    mul_nonneg (h.a_nonneg k) (div_nonneg (by positivity) (hs k).le))) h.dω_pos.le
  refine ⟨R₁ + R₂, fun z hz ℓ ↦ ?_⟩
  obtain ⟨hAz, hz0⟩ := hz
  rw [h.mulVec_eq_b_iff] at hAz
  have hzeq := h.eq_lift z
  rw [hAz.2] at hzeq
  set x := shieldPr s z
  have hx0 : ∀ k, 0 ≤ x k := h.nonneg_of_lift (t := 1) (hzeq ▸ hz0)
  have hxR : ∀ k, x k ≤ |R| := fun k ↦
    le_trans (le_abs_self _) (le_trans (hR x ⟨hAz.1, hx0⟩ k) (le_abs_self R))
  have hk : ∀ k, 2 * x k / s k ≤ 2 * |R| / s k := fun k ↦ by
    gcongr
    · exact (hs k).le
    · exact hxR k
  rw [abs_of_nonneg (hz0 ℓ), hzeq]
  induction ℓ using Fin.lastCases with
  | last =>
    rw [shieldLift_last]
    refine le_trans ?_ (le_add_of_nonneg_left hR₁)
    change _ ≤ (1 + ∑ k, a k * (2 * |R| / s k)) / dω
    gcongr with k
    all_goals first | exact h.dω_pos.le | exact h.a_nonneg k | exact (hs k).le | exact hxR k
  | cast k =>
    rw [shieldLift_castSucc]
    refine le_trans (hk k) (le_trans ?_ (le_add_of_nonneg_right hR₂))
    exact Finset.single_le_sum (f := fun k ↦ 2 * |R| / s k)
      (fun k _ ↦ div_nonneg (by positivity) (hs k).le) (mem_univ k)

theorem nondegenerate (hL : ∀ B, L.IsFeasibleBasis B → L.IsNondegenerate B) :
    ∀ B', L'.IsFeasibleBasis B' → L'.IsNondegenerate B' := by
  intro B' hB'
  obtain ⟨B, hB, rfl⟩ := (h.isFeasibleBasis_iff B').1 hB'
  intro ℓ hℓ
  rw [h.basicSol_hat hB.1]
  induction ℓ using Fin.lastCases with
  | last => exact h.lift_last_pos hB.2
  | cast k =>
    rw [shieldLift_castSucc]
    exact div_pos (by linarith [hL B hB k (by simpa using hℓ)]) (h.s_pos k)

theorem rank_eq {B₀ : Finset (Fin n)} (hB₀ : L.IsBasis B₀) : L'.A.rank = m + 1 := by
  have hB := h.isBasis_hat hB₀
  have hsurj : LinearMap.range L'.A.mulVecLin = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro r
    obtain ⟨x, hx, -⟩ := hB.exists_sol r
    exact ⟨x, by simpa using hx⟩
  rw [Matrix.rank, hsurj, finrank_top, Module.finrank_fin_fun]

/-- The basic direction of `j` at `B ∪ {ω}`. -/
theorem basicDir_hat {B : Finset (Fin n)} (hB : L.IsBasis B) {j : Fin n} (hj : j ∉ B) :
    L'.basicDir (hat B) j.castSucc = shieldLift s a dω 0 ((s j / 2) • L.basicDir B j) := by
  obtain ⟨h1, h2, h3⟩ := hB.basicDir_spec hj
  have hsj := (h.s_pos j).ne'
  refine ((h.isBasis_hat hB).eq_basicDir (by simpa using hj) ⟨?_, ?_, ?_⟩).symm
  · rw [h.mulVec_eq_zero_iff, h.pr_lift, h.row_lift, mulVec_smul, h1, smul_zero]
    exact ⟨rfl, rfl⟩
  · rw [shieldLift_castSucc, Pi.smul_apply, h2, smul_eq_mul, mul_one]
    field_simp
  · intro ℓ hℓ hℓj
    induction ℓ using Fin.lastCases with
    | last => exact absurd IntLP.last_mem_hat hℓ
    | cast k =>
      have hk : k ∉ B := by simpa using hℓ
      have hkj : k ≠ j := fun e ↦ hℓj (by rw [e])
      simp [h3 k hk hkj]

theorem reducedCost_hat {B : Finset (Fin n)} (hB : L.IsBasis B) (j : Fin n) :
    L'.reducedCost (hat B) j.castSucc = s j * κ * L.reducedCost B j := by
  by_cases hj : j ∈ B
  · rw [hB.reducedCost_of_mem hj, (h.isBasis_hat hB).reducedCost_of_mem (by simpa using hj)]
    ring
  · rw [← hB.cost_basicDir hj, ← (h.isBasis_hat hB).cost_basicDir (by simpa using hj),
      h.basicDir_hat hB hj]
    have hAd := (hB.basicDir_spec hj).1
    set d := L.basicDir B j
    have hu : ∑ k, (u ⬝ᵥ L.col k) * d k = 0 := by
      have : u ⬝ᵥ (L.A *ᵥ d) = 0 := by rw [hAd, dotProduct_zero]
      rw [dotProduct_mulVec] at this
      rw [← this]
      simp only [dotProduct, vecMul, col]
    rw [dotProduct, Fin.sum_univ_castSucc]
    simp only [h.c_c, h.c_l, zero_mul, add_zero, shieldLift_castSucc, Pi.smul_apply, smul_eq_mul]
    have : ∀ k, s k * (κ * L.c k - u ⬝ᵥ L.col k) * (2 * (s j / 2 * d k) / s k) =
        s j * κ * (L.c k * d k) - s j * ((u ⬝ᵥ L.col k) * d k) := fun k ↦ by
      have := (h.s_pos k).ne'
      field_simp
    simp only [this, Finset.sum_sub_distrib, ← Finset.mul_sum, hu, mul_zero, sub_zero]
    rfl

theorem improving_hat (hκ : 0 < κ) {B : Finset (Fin n)} (hB : L.IsBasis B) :
    L'.improving (hat B) = (L.improving B).map Fin.castSuccEmb := by
  ext ℓ
  induction ℓ using Fin.lastCases with
  | last =>
    simp only [improving, mem_filter, mem_univ, true_and, mem_map, Fin.castSuccEmb_apply,
      Fin.castSucc_ne_last, and_false, exists_false, iff_false, not_lt]
    rw [(h.isBasis_hat hB).reducedCost_of_mem IntLP.last_mem_hat]
  | cast k =>
    simp only [improving, mem_filter, mem_univ, true_and, mem_map, Fin.castSuccEmb_apply,
      Fin.castSucc_inj, exists_eq_right]
    rw [h.reducedCost_hat hB]
    have := mul_pos (h.s_pos k) hκ
    constructor
    · intro H; by_contra H'; push Not at H'; nlinarith
    · intro H; nlinarith

/-- Leaving labels correspond (the shield `ω` never leaves). -/
theorem isLeavingLabel_hat_iff (hL : L.FeasibleSetNonemptyBounded) {B : Finset (Fin n)}
    (hB : L.IsFeasibleBasis B) {j : Fin n} (hj : j ∈ L.improving B) (i' : Fin (n + 1)) :
    L'.IsLeavingLabel (hat B) j.castSucc i' ↔ ∃ i, i' = i.castSucc ∧ L.IsLeavingLabel B j i := by
  have hjB := hB.1.not_mem_of_mem_improving hj
  have hx' := h.basicSol_hat hB.1
  have hd' := h.basicDir_hat hB.1 hjB
  set x := L.basicSol B
  set d := L.basicDir B j
  have hsj := h.s_pos j
  have hdc : ∀ k, L'.basicDir (hat B) j.castSucc k.castSucc = s j / s k * d k := by
    intro k
    have := (h.s_pos k).ne'
    rw [hd', shieldLift_castSucc, Pi.smul_apply, smul_eq_mul]
    field_simp
  have hxc : ∀ k, L'.basicSol (hat B) k.castSucc = 2 * x k / s k := by
    intro k; rw [hx', shieldLift_castSucc]
  have hneg : ∀ k, L'.basicDir (hat B) j.castSucc k.castSucc < 0 ↔ d k < 0 := by
    intro k
    rw [hdc]
    have := div_pos hsj (h.s_pos k)
    constructor
    · intro H; by_contra H'; push Not at H'; nlinarith
    · intro H; nlinarith
  have hratio : ∀ k, d k < 0 → L'.basicSol (hat B) k.castSucc /
      (-L'.basicDir (hat B) j.castSucc k.castSucc) = 2 / s j * (x k / (-d k)) := by
    intro k hk
    have := (h.s_pos k).ne'
    have := hk.ne
    rw [hxc, hdc]
    field_simp
  have key : ∀ i₀, L.IsLeavingLabel B j i₀ →
      L'.basicDir (hat B) j.castSucc (Fin.last n) < 0 →
      2 / s j * (x i₀ / (-d i₀)) < L'.basicSol (hat B) (Fin.last n) /
        (-L'.basicDir (hat B) j.castSucc (Fin.last n)) := by
    intro i₀ hi₀ hω
    obtain ⟨hfeas, heq⟩ := L.pivot_spec hB hj hi₀
    set θ := x i₀ / (-d i₀)
    have hnn : ∀ k, 0 ≤ (x + θ • d) k := by intro k; rw [← heq]; exact hfeas.2 k
    set r := 2 / s j * θ with hr
    have hz : L'.basicSol (hat B) + r • L'.basicDir (hat B) j.castSucc =
        shieldLift s a dω 1 (x + θ • d) := by
      rw [h.eq_lift (L'.basicSol (hat B) + r • _), shieldRow_add_smul, shieldPr_add_smul, hx', hd',
        h.row_lift, h.row_lift, h.pr_lift, h.pr_lift, smul_smul,
        show r * (s j / 2) = θ by rw [hr]; field_simp]
      congr 1
      ring
    have hpos := h.lift_last_pos hnn
    rw [← hz] at hpos
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hpos
    rw [lt_div_iff₀ (by linarith)]
    linarith
  constructor
  · rintro ⟨hi'B, hi'd, hmin⟩
    obtain ⟨i₀, hi₀⟩ := L.exists_leavingLabel hL hB hj
    induction i' using Fin.lastCases with
    | last =>
      exfalso
      have h1 := key i₀ hi₀ hi'd
      have h2 := hmin i₀.castSucc (by simpa using hi₀.1) ((hneg i₀).2 hi₀.2.1)
      rw [hratio i₀ hi₀.2.1] at h2
      linarith
    | cast i =>
      refine ⟨i, rfl, by simpa using hi'B, (hneg i).1 hi'd, fun k hk hdk ↦ ?_⟩
      have h2 := hmin k.castSucc (by simpa using hk) ((hneg k).2 hdk)
      rw [hratio i ((hneg i).1 hi'd), hratio k hdk] at h2
      exact le_of_mul_le_mul_left h2 (by positivity)
  · rintro ⟨i, rfl, hi⟩
    refine ⟨by simpa using hi.1, (hneg i).2 hi.2.1, fun k' hk' hdk' ↦ ?_⟩
    rw [hratio i hi.2.1]
    induction k' using Fin.lastCases with
    | last => exact (key i hi hdk').le
    | cast k =>
      rw [hratio k ((hneg k).1 hdk')]
      exact mul_le_mul_of_nonneg_left (hi.2.2 k (by simpa using hk') ((hneg k).1 hdk'))
        (by positivity)

end IsShieldOf

end LP

end WolfeSimplex

namespace WolfeSimplex

open Finset Matrix

namespace IntLP

variable {m n : ℕ} (P : IntLP m n) (e : Fin m → Fin n)

/-! ### Entries of (LP⁺) and (LP̃⁺) -/

@[simp] lemma shieldLP_A_cc (i : Fin m) (k : Fin n) :
    (P.shieldLP e).A i.castSucc k.castSucc = (P.canonical e).A i k := by simp [shieldLP]

@[simp] lemma shieldLP_A_cl (i : Fin m) : (P.shieldLP e).A i.castSucc (Fin.last n) = 0 := by
  simp [shieldLP]

@[simp] lemma shieldLP_A_lc (k : Fin n) :
    (P.shieldLP e).A (Fin.last m) k.castSucc =
      if k ∈ basisOf e then 0 else -P.shieldCoeff e := by simp [shieldLP]

@[simp] lemma shieldLP_A_ll : (P.shieldLP e).A (Fin.last m) (Fin.last n) = P.Delta0 e := by
  simp [shieldLP]

@[simp] lemma shieldLP_b_c (i : Fin m) : (P.shieldLP e).b i.castSucc = (P.canonical e).b i := by
  simp [shieldLP]

@[simp] lemma shieldLP_b_l : (P.shieldLP e).b (Fin.last m) = 1 := by simp [shieldLP]

@[simp] lemma shieldLP_c_c (k : Fin n) : (P.shieldLP e).c k.castSucc = (P.canonical e).c k := by
  simp [shieldLP]

@[simp] lemma shieldLP_c_l : (P.shieldLP e).c (Fin.last n) = 0 := by simp [shieldLP]

omit P e in
@[simp] lemma shieldRank_castSucc (σ : Equiv.Perm (Fin n)) (k : Fin n) :
    shieldRank σ k.castSucc = (σ k : ℕ) + 1 := by simp [shieldRank]

omit P e in
@[simp] lemma shieldRank_last (σ : Equiv.Perm (Fin n)) : shieldRank σ (Fin.last n) = n + 1 := by
  simp [shieldRank]

variable (σ : Equiv.Perm (Fin n))

@[simp] lemma weightedLP_A_cc (i : Fin m) (k : Fin n) :
    (P.weightedLP e σ).A i.castSucc k.castSucc =
      if k ∈ basisOf e then (if e i = k then (shieldRank σ k.castSucc : ℤ) * P.shieldW e else 0)
      else (P.canonical e).A i k := by
  simp only [weightedLP, of_apply, Fin.snoc_castSucc, shieldRank_castSucc]

@[simp] lemma weightedLP_A_cl (i : Fin m) : (P.weightedLP e σ).A i.castSucc (Fin.last n) = 0 := by
  simp [weightedLP]

@[simp] lemma weightedLP_A_lc (k : Fin n) :
    (P.weightedLP e σ).A (Fin.last m) k.castSucc =
      if k ∈ basisOf e then 0 else -((shieldRank σ k.castSucc : ℤ) * P.shieldW e) := by
  simp only [weightedLP, of_apply, Fin.snoc_last, Fin.snoc_castSucc, shieldRank_castSucc]

@[simp] lemma weightedLP_A_ll :
    (P.weightedLP e σ).A (Fin.last m) (Fin.last n) =
      (shieldRank σ (Fin.last n) : ℤ) * P.shieldW e := by
  simp only [weightedLP, of_apply, Fin.snoc_last]

@[simp] lemma weightedLP_b : (P.weightedLP e σ).b = (P.shieldLP e).b := rfl

@[simp] lemma weightedLP_c : (P.weightedLP e σ).c = (P.shieldLP e).c := rfl

/-! ### The matrix `G` -/

lemma canonG_mul_basisMat : P.canonG e * P.basisMat e = P.Delta0 e • (1 : Matrix _ _ ℤ) := by
  simp only [canonG, Delta0, Matrix.smul_mul, adjugate_mul, smul_smul, Int.sign_mul_self_eq_abs]

lemma basisMat_mul_canonG : P.basisMat e * P.canonG e = P.Delta0 e • (1 : Matrix _ _ ℤ) := by
  simp only [canonG, Delta0, Matrix.mul_smul, mul_adjugate, smul_smul, Int.sign_mul_self_eq_abs]

/-- `G` over `ℝ`. -/
noncomputable def Gr : Matrix (Fin m) (Fin m) ℝ := (P.canonG e).map (Int.cast : ℤ → ℝ)

/-- `A_{B₀}` over `ℝ`. -/
noncomputable def Mr : Matrix (Fin m) (Fin m) ℝ := (P.basisMat e).map (Int.cast : ℤ → ℝ)

/-- `u = Gᵀ c_{B₀}` (so that `c' = Δ₀ c - Aᵀ u`). -/
noncomputable def uVec : Fin m → ℝ := fun l ↦ ∑ i, (P.canonG e i l : ℝ) * (P.c (e i) : ℝ)

lemma Gr_mul_Mr : P.Gr e * P.Mr e = (P.Delta0 e : ℝ) • (1 : Matrix _ _ ℝ) := by
  ext i k
  have := congrFun (congrFun (P.canonG_mul_basisMat e) i) k
  simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at this
  simp only [Gr, Mr, Matrix.mul_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul]
  by_cases hik : i = k
  · subst hik; simp only [ite_true, mul_one] at this ⊢; exact_mod_cast this
  · simp only [hik, ite_false, mul_zero] at this ⊢; exact_mod_cast this

lemma Mr_mul_Gr : P.Mr e * P.Gr e = (P.Delta0 e : ℝ) • (1 : Matrix _ _ ℝ) := by
  ext i k
  have := congrFun (congrFun (P.basisMat_mul_canonG e) i) k
  simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at this
  simp only [Gr, Mr, Matrix.mul_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul]
  by_cases hik : i = k
  · subst hik; simp only [ite_true, mul_one] at this ⊢; exact_mod_cast this
  · simp only [hik, ite_false, mul_zero] at this ⊢; exact_mod_cast this

lemma e_injective (hB₀ : P.toLP.IsBasis (basisOf e)) : Function.Injective e := by
  have h : (univ.image e).card = (univ : Finset (Fin m)).card := by
    rw [card_univ, Fintype.card_fin]; exact hB₀.1
  intro x y hxy
  exact Finset.card_image_iff.1 h (mem_coe.2 (mem_univ x)) (mem_coe.2 (mem_univ y)) hxy

omit P in
lemma mem_basisOf {k : Fin n} : k ∈ basisOf e ↔ ∃ i, e i = k := by simp [basisOf]

/-- Extension of `v : ℝ^{B₀}` by zeros. -/
noncomputable def extE (v : Fin m → ℝ) : Fin n → ℝ := fun k ↦ ∑ i, if e i = k then v i else 0

omit P in
lemma extE_apply (hinj : Function.Injective e) (v : Fin m → ℝ) (i : Fin m) :
    extE e v (e i) = v i := by
  simp [extE, hinj.eq_iff]

omit P in
lemma extE_eq_zero (v : Fin m → ℝ) {k : Fin n} (hk : k ∉ basisOf e) : extE e v k = 0 :=
  Finset.sum_eq_zero fun i _ ↦ by
    rw [ite_eq_right_iff]; rintro rfl; exact absurd ((mem_basisOf e).2 ⟨i, rfl⟩) hk

lemma toLP_A_mulVec_extE (v : Fin m → ℝ) : P.toLP.A *ᵥ extE e v = P.Mr e *ᵥ v := by
  ext l
  simp only [mulVec, dotProduct, extE, Finset.mul_sum, Mr, basisMat, map_apply, of_apply, toLP_A]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp [mul_ite]

lemma Delta0_pos (hB₀ : P.toLP.IsBasis (basisOf e)) : 0 < P.Delta0 e := by
  have hinj := P.e_injective e hB₀
  unfold Delta0
  rw [abs_pos]
  intro hdet
  have hdetR : (P.Mr e).det = 0 := by
    have := RingHom.map_det (Int.castRingHom ℝ) (P.basisMat e)
    rw [hdet, map_zero] at this
    rw [this]; rfl
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdetR
  have hx := hB₀.eq_zero (x := extE e v) (fun k hk ↦ extE_eq_zero e v hk)
    (by rw [toLP_A_mulVec_extE, hv])
  apply hv0
  funext i
  rw [← extE_apply e hinj v i, hx]; rfl

lemma Gr_inj (hB₀ : P.toLP.IsBasis (basisOf e)) (v : Fin m → ℝ) (hv : P.Gr e *ᵥ v = 0) :
    v = 0 := by
  have h1 : (P.Mr e * P.Gr e) *ᵥ v = 0 := by rw [← mulVec_mulVec, hv, mulVec_zero]
  rw [Mr_mul_Gr, smul_mulVec, one_mulVec] at h1
  exact (smul_eq_zero.1 h1).resolve_left (by exact_mod_cast (P.Delta0_pos e hB₀).ne')

lemma canonical_A_real (i : Fin m) (k : Fin n) :
    ((P.canonical e).A i k : ℝ) = (P.Gr e * P.toLP.A) i k := by
  simp [canonical, Gr, Matrix.mul_apply]

lemma canonical_b_real (i : Fin m) :
    ((P.canonical e).b i : ℝ) = 2 * (P.Gr e *ᵥ P.toLP.b) i := by
  simp [canonical, Gr, mulVec, dotProduct]

lemma canonical_c_real (k : Fin n) :
    ((P.canonical e).c k : ℝ) = P.Delta0 e * P.toLP.c k - P.uVec e ⬝ᵥ P.toLP.col k := by
  simp only [canonical, uVec, Matrix.mul_apply, dotProduct, toLP_c, toLP_col]
  push_cast
  congr 1
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring

set_option linter.unusedVariables false in
lemma canonical_A_apply_e (hB₀ : P.toLP.IsBasis (basisOf e)) (i k : Fin m) :
    (P.canonical e).A i (e k) = if i = k then P.Delta0 e else 0 := by
  have := congrFun (congrFun (P.canonG_mul_basisMat e) i) k
  simp only [Matrix.mul_apply, basisMat, of_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero] at this
  simp only [canonical, Matrix.mul_apply]
  exact this

lemma canonical_c_apply_e (hB₀ : P.toLP.IsBasis (basisOf e)) (k : Fin m) :
    (P.canonical e).c (e k) = 0 := by
  have h := P.canonical_A_apply_e e hB₀
  simp only [canonical] at h ⊢
  simp [h, ite_mul]

lemma two_le_canonical_b (hP : P.IsAdmissible) (hB₀ : P.toLP.IsFeasibleBasis (basisOf e))
    (i : Fin m) : 2 ≤ (P.canonical e).b i := by
  have hinj := P.e_injective e hB₀.1
  obtain ⟨hAx, hx0⟩ := hB₀.1.basicSol_spec
  set x := P.toLP.basicSol (basisOf e)
  have hxe : x = extE e (x ∘ e) := by
    funext k
    by_cases hk : k ∈ basisOf e
    · obtain ⟨i, rfl⟩ := (mem_basisOf e).1 hk
      rw [extE_apply e hinj]; rfl
    · rw [hx0 k hk, extE_eq_zero e _ hk]
  have hb : P.toLP.b = P.Mr e *ᵥ (x ∘ e) := by
    rw [← hAx]; conv_lhs => rw [hxe]
    rw [toLP_A_mulVec_extE]
  have hGb : ((P.canonG e *ᵥ P.b) i : ℝ) = P.Delta0 e * x (e i) := by
    have : ((P.canonG e *ᵥ P.b) i : ℝ) = (P.Gr e *ᵥ P.toLP.b) i := by
      simp [Gr, mulVec, dotProduct]
    rw [this, hb, mulVec_mulVec, Gr_mul_Mr, smul_mulVec, one_mulVec]
    simp
  have hpos : 0 < ((P.canonG e *ᵥ P.b) i : ℝ) := by
    rw [hGb]
    exact mul_pos (by exact_mod_cast P.Delta0_pos e hB₀.1)
      (hP.2.2.2 _ hB₀ (e i) ((mem_basisOf e).2 ⟨i, rfl⟩))
  have : 0 < (P.canonG e *ᵥ P.b) i := by exact_mod_cast hpos
  simp only [canonical]
  omega

/-! ### The shield coefficients -/

lemma shieldCoeff_ge : P.Delta0 e ≤ P.shieldCoeff e := by
  unfold shieldCoeff
  exact le_add_of_nonneg_right (Nat.cast_nonneg _)

set_option linter.unusedVariables false in
lemma shield_sum_le (hP : P.IsAdmissible) (hB₀ : P.toLP.IsFeasibleBasis (basisOf e))
    (k : Fin n) (hk : k ∉ basisOf e) :
    ∑ i, (P.canonical e).b i * max ((P.canonical e).A i k) 0 ≤ P.shieldCoeff e - P.Delta0 e := by
  unfold shieldCoeff
  rw [add_sub_cancel_left]
  refine le_trans (Int.self_le_toNat _) ?_
  exact_mod_cast Finset.le_sup (f := fun k ↦
    (∑ i, (P.canonical e).b i * max ((P.canonical e).A i k) 0).toNat) (by simp [hk])

lemma shieldW_ge : P.shieldCoeff e ≤ P.shieldW e := by
  unfold shieldW
  exact le_add_of_nonneg_right (Nat.cast_nonneg _)

lemma shieldW_sum_le (k : Fin n) (hk : k ∉ basisOf e) :
    ∑ i, (P.canonical e).A i k ^ 2 ≤ P.shieldW e - P.shieldCoeff e := by
  unfold shieldW
  rw [add_sub_cancel_left]
  refine le_trans (Int.self_le_toNat _) ?_
  have h := Finset.le_sup (s := univ.filter fun k ↦ k ∉ basisOf e)
    (f := fun k ↦ (∑ i, (P.canonical e).A i k ^ 2).toNat) (by simp [hk] : k ∈ _)
  exact_mod_cast h

/-! ### (LP⁺) and (LP̃⁺) have the shield shape -/

lemma isShield (hB₀ : P.toLP.IsBasis (basisOf e)) :
    P.toLP.IsShieldOf (P.shieldLP e).toLP (P.Gr e) 1 (P.Delta0 e) (P.uVec e)
      (fun k ↦ if k ∈ basisOf e then 0 else (P.shieldCoeff e : ℝ)) (P.Delta0 e) where
  G_inj := P.Gr_inj e hB₀
  s_pos _ := one_pos
  a_nonneg k := by
    have := (P.Delta0_pos e hB₀).le.trans (P.shieldCoeff_ge e)
    split_ifs
    · exact le_rfl
    · exact_mod_cast this
  dω_pos := by exact_mod_cast P.Delta0_pos e hB₀
  A_cc i k := by simp [canonical_A_real]
  A_cl i := by simp
  A_lc k := by simp only [toLP_A, shieldLP_A_lc]; split_ifs <;> simp
  A_ll := by simp
  b_c i := by simp [canonical_b_real]
  b_l := by simp
  c_c k := by simp [canonical_c_real]
  c_l := by simp

lemma shieldW_pos (hB₀ : P.toLP.IsBasis (basisOf e)) : 0 < P.shieldW e :=
  (P.Delta0_pos e hB₀).trans_le ((P.shieldCoeff_ge e).trans (P.shieldW_ge e))

lemma isShieldW (hB₀ : P.toLP.IsBasis (basisOf e)) :
    P.toLP.IsShieldOf (P.weightedLP e σ).toLP (P.Gr e)
      (fun k ↦ if k ∈ basisOf e then (shieldRank σ k.castSucc : ℝ) * P.shieldW e / P.Delta0 e
        else 1)
      (P.Delta0 e) (P.uVec e)
      (fun k ↦ if k ∈ basisOf e then 0 else (shieldRank σ k.castSucc : ℝ) * P.shieldW e)
      ((shieldRank σ (Fin.last n) : ℝ) * P.shieldW e) where
  G_inj := P.Gr_inj e hB₀
  s_pos k := by
    have h1 : (0 : ℝ) < P.shieldW e := by exact_mod_cast P.shieldW_pos e hB₀
    have h2 : (0 : ℝ) < P.Delta0 e := by exact_mod_cast P.Delta0_pos e hB₀
    split_ifs
    · simp only [shieldRank_castSucc]; positivity
    · exact one_pos
  a_nonneg k := by
    have h1 : (0 : ℝ) < P.shieldW e := by exact_mod_cast P.shieldW_pos e hB₀
    split_ifs
    · exact le_rfl
    · positivity
  dω_pos := by
    have h1 : (0 : ℝ) < P.shieldW e := by exact_mod_cast P.shieldW_pos e hB₀
    simp only [shieldRank_last]; positivity
  A_cc i k := by
    have hinj := P.e_injective e hB₀
    have h2 : (P.Delta0 e : ℝ) ≠ 0 := by exact_mod_cast (P.Delta0_pos e hB₀).ne'
    by_cases hk : k ∈ basisOf e
    · obtain ⟨i', rfl⟩ := (mem_basisOf e).1 hk
      rw [← canonical_A_real, P.canonical_A_apply_e e hB₀]
      simp only [toLP_A, weightedLP_A_cc, hk, ite_true, hinj.eq_iff]
      split_ifs <;> simp [h2]
    · simp [hk, canonical_A_real]
  A_cl i := by simp
  A_lc k := by simp only [toLP_A, weightedLP_A_lc]; split_ifs <;> simp
  A_ll := by simp
  b_c i := by simp [canonical_b_real]
  b_l := by simp
  c_c k := by
    simp only [toLP_c, weightedLP_c, shieldLP_c_c]
    rw [canonical_c_real]
    by_cases hk : k ∈ basisOf e
    · obtain ⟨i', rfl⟩ := (mem_basisOf e).1 hk
      have h0 := P.canonical_c_apply_e e hB₀ i'
      have h1 : ((P.canonical e).c (e i') : ℝ) = 0 := by rw [h0]; simp
      rw [canonical_c_real] at h1
      simp only [toLP_c] at h1 ⊢
      rw [h1]; simp
    · simp [hk]
  c_l := by simp

lemma isAdmissible_of_isShield {Q : IntLP (m + 1) (n + 1)} {G : Matrix (Fin m) (Fin m) ℝ}
    {s : Fin n → ℝ} {κ : ℝ} {u : Fin m → ℝ} {a : Fin n → ℝ} {dω : ℝ}
    (h : P.toLP.IsShieldOf Q.toLP G s κ u a dω) (hP : P.IsAdmissible)
    (hB₀ : P.toLP.IsBasis (basisOf e)) : Q.IsAdmissible :=
  ⟨by omega, h.rank_eq hB₀, h.feasibleSetNonemptyBounded hP.2.2.1, h.nondegenerate hP.2.2.2⟩

lemma shieldLP_isAdmissible (hP : P.IsAdmissible) (hB₀ : P.toLP.IsFeasibleBasis (basisOf e)) :
    (P.shieldLP e).IsAdmissible :=
  P.isAdmissible_of_isShield e (P.isShield e hB₀.1) hP hB₀.1

lemma weightedLP_isAdmissible (hP : P.IsAdmissible) (hB₀ : P.toLP.IsFeasibleBasis (basisOf e))
    (σ : Equiv.Perm (Fin n)) : (P.weightedLP e σ).IsAdmissible :=
  P.isAdmissible_of_isShield e (P.isShieldW e σ hB₀.1) hP hB₀.1

/-! ### Size of (LP⁺) and (LP̃⁺) -/

lemma abs_A_le_W (i : Fin m) (j : Fin n) : |P.A i j| ≤ P.maxEntry := by
  have := (P.natAbs_A_le i j).trans P.U_le_maxEntry
  rw [Int.abs_eq_natAbs]; exact_mod_cast this

lemma abs_b_le_W (i : Fin m) : |P.b i| ≤ P.maxEntry := by
  have := (P.natAbs_b_le i).trans P.U_le_maxEntry
  rw [Int.abs_eq_natAbs]; exact_mod_cast this

lemma abs_c_le_W (j : Fin n) : |P.c j| ≤ P.maxEntry := by
  have := (P.natAbs_c_le j).trans P.sup_c_le_maxEntry
  rw [Int.abs_eq_natAbs]; exact_mod_cast this

/-- `F = m! W^m`, the bound for all `m × m` determinants of entries of size `≤ W`. -/
def detBd : ℕ := m.factorial * P.maxEntry ^ m

lemma abs_det_le_detBd (Q : Matrix (Fin m) (Fin m) ℤ) (hQ : ∀ i j, |Q i j| ≤ P.maxEntry) :
    |Q.det| ≤ P.detBd := by
  have h := Matrix.det_le (abv := AbsoluteValue.abs) (x := (P.maxEntry : ℤ)) (A := Q) hQ
  simp only [AbsoluteValue.abs_apply, nsmul_eq_mul, Fintype.card_fin] at h
  simpa [detBd] using h

lemma Delta0_nonneg : 0 ≤ P.Delta0 e := abs_nonneg _

lemma Delta0_le : P.Delta0 e ≤ P.detBd :=
  P.abs_det_le_detBd _ fun i k ↦ by simpa [basisMat] using P.abs_A_le_W i (e k)

omit P e in
lemma abs_sign_le_one (a : ℤ) : |a.sign| ≤ 1 := by
  rcases lt_trichotomy a 0 with h | h | h
  · simp [Int.sign_eq_neg_one_of_neg h]
  · simp [h]
  · simp [Int.sign_eq_one_of_pos h]

lemma abs_canonG_mulVec_le (v : Fin m → ℤ) (hv : ∀ l, |v l| ≤ P.maxEntry) (i : Fin m) :
    |(P.canonG e *ᵥ v) i| ≤ P.detBd := by
  have h : P.canonG e *ᵥ v = (P.basisMat e).det.sign • (P.basisMat e).cramer v := by
    rw [canonG, smul_mulVec, cramer_eq_adjugate_mulVec]
  rw [h, Pi.smul_apply, smul_eq_mul, cramer_apply, abs_mul]
  have hd : |((P.basisMat e).updateCol i v).det| ≤ P.detBd := by
    refine P.abs_det_le_detBd _ fun a b ↦ ?_
    rw [updateCol_apply]
    split_ifs
    · exact hv a
    · simpa [basisMat] using P.abs_A_le_W a (e b)
  calc _ ≤ 1 * (P.detBd : ℤ) := mul_le_mul (abs_sign_le_one _) hd (abs_nonneg _) zero_le_one
    _ = _ := one_mul _

lemma abs_canonical_A_le (i : Fin m) (k : Fin n) : |(P.canonical e).A i k| ≤ P.detBd := by
  have : (P.canonical e).A i k = (P.canonG e *ᵥ fun l ↦ P.A l k) i := by
    simp [canonical, Matrix.mul_apply, mulVec, dotProduct]
  rw [this]; exact P.abs_canonG_mulVec_le e _ (fun l ↦ P.abs_A_le_W l k) i

lemma abs_canonical_b_le (i : Fin m) : |(P.canonical e).b i| ≤ 2 * P.detBd := by
  have := P.abs_canonG_mulVec_le e P.b P.abs_b_le_W i
  simp only [canonical, abs_mul, abs_two]
  linarith

lemma abs_canonical_c_le (k : Fin n) :
    |(P.canonical e).c k| ≤ (m + 1) * P.detBd * P.maxEntry := by
  have hF : (0 : ℤ) ≤ P.detBd := Nat.cast_nonneg _
  have hW : (0 : ℤ) ≤ P.maxEntry := Nat.cast_nonneg _
  have h1 : |P.Delta0 e * P.c k| ≤ P.detBd * P.maxEntry := by
    rw [abs_mul, abs_of_nonneg (P.Delta0_nonneg e)]
    exact mul_le_mul (P.Delta0_le e) (P.abs_c_le_W k) (abs_nonneg _) hF
  have h2 : |∑ i, (P.canonical e).A i k * P.c (e i)| ≤ m * (P.detBd * P.maxEntry) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |(P.canonical e).A i k * P.c (e i)|
        ≤ ∑ _i : Fin m, ((P.detBd : ℤ) * P.maxEntry) := by
          refine Finset.sum_le_sum fun i _ ↦ ?_
          rw [abs_mul]
          exact mul_le_mul (P.abs_canonical_A_le e i k) (P.abs_c_le_W _) (abs_nonneg _) hF
      _ = _ := by simp
  have h3 : |(P.canonical e).c k| ≤
      |P.Delta0 e * P.c k| + |∑ i, (P.canonical e).A i k * P.c (e i)| := abs_sub _ _
  nlinarith

lemma shieldCoeff_nonneg : 0 ≤ P.shieldCoeff e := (P.Delta0_nonneg e).trans (P.shieldCoeff_ge e)

lemma shieldCoeff_le : P.shieldCoeff e ≤ P.detBd + 2 * m * P.detBd ^ 2 := by
  have hF : (0 : ℤ) ≤ P.detBd := Nat.cast_nonneg _
  have hsup : ((univ.filter fun k ↦ k ∉ basisOf e).sup fun k ↦
      (∑ i, (P.canonical e).b i * max ((P.canonical e).A i k) 0).toNat) ≤
        2 * m * P.detBd ^ 2 := by
    refine Finset.sup_le fun k _ ↦ ?_
    rw [Int.toNat_le]; push_cast
    calc ∑ i, (P.canonical e).b i * max ((P.canonical e).A i k) 0
        ≤ ∑ _i : Fin m, 2 * (P.detBd : ℤ) * P.detBd := by
          refine Finset.sum_le_sum fun i _ ↦ ?_
          have hb := P.abs_canonical_b_le e i
          have hA := P.abs_canonical_A_le e i k
          have h0 : 0 ≤ max ((P.canonical e).A i k) 0 := le_max_right _ _
          have h1 : max ((P.canonical e).A i k) 0 ≤ P.detBd :=
            max_le ((le_abs_self _).trans hA) hF
          calc (P.canonical e).b i * max ((P.canonical e).A i k) 0
              ≤ |(P.canonical e).b i| * max ((P.canonical e).A i k) 0 :=
                mul_le_mul_of_nonneg_right (le_abs_self _) h0
            _ ≤ 2 * (P.detBd : ℤ) * P.detBd := mul_le_mul hb h1 h0 (by positivity)
      _ = _ := by simp; ring
  have hsup' : (((univ.filter fun k ↦ k ∉ basisOf e).sup fun k ↦
      (∑ i, (P.canonical e).b i * max ((P.canonical e).A i k) 0).toNat : ℕ) : ℤ) ≤
        2 * m * P.detBd ^ 2 := by exact_mod_cast hsup
  unfold shieldCoeff
  linarith [P.Delta0_le e]

lemma shieldW_le : P.shieldW e ≤ P.detBd + 3 * m * P.detBd ^ 2 := by
  have hsup : ((univ.filter fun k ↦ k ∉ basisOf e).sup fun k ↦
      (∑ i, (P.canonical e).A i k ^ 2).toNat) ≤ m * P.detBd ^ 2 := by
    refine Finset.sup_le fun k _ ↦ ?_
    rw [Int.toNat_le]; push_cast
    calc ∑ i, (P.canonical e).A i k ^ 2 ≤ ∑ _i : Fin m, (P.detBd : ℤ) ^ 2 := by
          refine Finset.sum_le_sum fun i _ ↦ ?_
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (P.abs_canonical_A_le e i k) 2
      _ = _ := by simp
  have hsup' : (((univ.filter fun k ↦ k ∉ basisOf e).sup fun k ↦
      (∑ i, (P.canonical e).A i k ^ 2).toNat : ℕ) : ℤ) ≤ m * P.detBd ^ 2 := by
    exact_mod_cast hsup
  unfold shieldW
  linarith [P.shieldCoeff_le e]

lemma detBd_le : P.detBd ≤ ((m + 1) * P.maxEntry) ^ m := by
  unfold detBd
  rw [mul_pow]
  exact Nat.mul_le_mul ((Nat.factorial_le_pow m).trans (Nat.pow_le_pow_left (by omega) m)) le_rfl

omit P e in
lemma maxEntry_le_of {m' n' : ℕ} (Q : IntLP m' n') (N : ℕ) (h2 : 2 ≤ N)
    (hA : ∀ i j, |Q.A i j| ≤ N) (hb : ∀ i, |Q.b i| ≤ N) (hc : ∀ j, |Q.c j| ≤ N) :
    Q.maxEntry ≤ N := by
  have cv : ∀ z : ℤ, |z| ≤ N → z.natAbs ≤ N := fun z hz ↦ by
    rw [Int.abs_eq_natAbs] at hz; exact_mod_cast hz
  unfold maxEntry
  exact max_le h2 (max_le (max_le (Finset.sup_le fun ij _ ↦ cv _ (hA ij.1 ij.2))
    (Finset.sup_le fun i _ ↦ cv _ (hb i))) (Finset.sup_le fun j _ ↦ cv _ (hc j)))

omit P e in
lemma arith_bounds (m F W Y Z : ℤ) (hm : 1 ≤ m) (hW : 2 ≤ W) (hY : Y = (m + 1) * W)
    (hF0 : 0 ≤ F) (hFZ : F ≤ Z) (hZ : 1 ≤ Z) :
    2 ≤ Y ^ 2 * Z ^ 2 ∧ F + 3 * m * F ^ 2 ≤ Y ^ 2 * Z ^ 2 ∧ (m + 1) * F * W ≤ Y ^ 2 * Z ^ 2 ∧
      2 * F ≤ Y ^ 2 * Z ^ 2 := by
  have hY4 : 4 ≤ Y := by rw [hY]; nlinarith
  have hYm : 3 * m + 1 ≤ Y ^ 2 := by nlinarith
  have hY16 : 16 ≤ Y ^ 2 := by nlinarith
  have hZ2 : Z ≤ Z ^ 2 := by nlinarith
  have hZ1 : 1 ≤ Z ^ 2 := by nlinarith
  have hF2 : F ^ 2 ≤ Z ^ 2 := pow_le_pow_left₀ hF0 hFZ 2
  have hYZ : Y * Z ≤ Y ^ 2 * Z ^ 2 := by
    have h1 : 1 ≤ Y * Z := by nlinarith
    rw [show Y ^ 2 * Z ^ 2 = (Y * Z) ^ 2 by ring]
    nlinarith
  refine ⟨by nlinarith, ?_, ?_, by nlinarith⟩
  · have h1 : 3 * m * F ^ 2 ≤ 3 * m * Z ^ 2 := mul_le_mul_of_nonneg_left hF2 (by linarith)
    have h2 : (3 * m + 1) * Z ^ 2 ≤ Y ^ 2 * Z ^ 2 := mul_le_mul_of_nonneg_right hYm (by positivity)
    nlinarith
  · rw [show (m + 1) * F * W = Y * F by rw [hY]; ring]
    have : Y * F ≤ Y * Z := mul_le_mul_of_nonneg_left hFZ (by linarith)
    linarith

/-- The common bound: all entries of the canonical part and the shield coefficient are at
most `((m+1) W)^{2m+2}`. -/
lemma entry_bounds (hm : 1 ≤ m) :
    let T : ℤ := (((m + 1) * P.maxEntry) ^ (2 * m + 2) : ℕ)
    2 ≤ T ∧ (P.detBd : ℤ) + 3 * m * P.detBd ^ 2 ≤ T ∧ (m + 1) * P.detBd * P.maxEntry ≤ T ∧
      2 * (P.detBd : ℤ) ≤ T ∧ (P.detBd : ℤ) ≤ T := by
  intro T
  have hW : (2 : ℤ) ≤ P.maxEntry := by exact_mod_cast P.two_le_maxEntry
  have hFZ : (P.detBd : ℤ) ≤ ((m + 1) * P.maxEntry : ℤ) ^ m := by exact_mod_cast P.detBd_le
  have hT : T = ((m + 1) * P.maxEntry : ℤ) ^ 2 * (((m + 1) * P.maxEntry : ℤ) ^ m) ^ 2 := by
    simp only [T]; push_cast; ring
  have hZ : (1 : ℤ) ≤ ((m + 1) * P.maxEntry : ℤ) ^ m := one_le_pow₀ (by nlinarith)
  obtain ⟨h1, h2, h3, h4⟩ := arith_bounds m P.detBd P.maxEntry _ _ (by exact_mod_cast hm) hW rfl
    (Nat.cast_nonneg _) hFZ hZ
  rw [hT]
  refine ⟨h1, h2, h3, h4, ?_⟩
  have : (0 : ℤ) ≤ P.detBd := Nat.cast_nonneg _
  linarith

lemma shieldLP_maxEntry_le (hm : 1 ≤ m) :
    (P.shieldLP e).maxEntry ≤ ((m + 1) * P.maxEntry) ^ (2 * m + 2) := by
  obtain ⟨h2, ha, hc, hb, hF⟩ := P.entry_bounds hm
  have hF0 : (0 : ℤ) ≤ P.detBd := Nat.cast_nonneg _
  have hm0 : (0 : ℤ) ≤ m := Nat.cast_nonneg _
  have hcoef := P.shieldCoeff_le e
  have hcoef0 := P.shieldCoeff_nonneg e
  have hD := P.Delta0_le e
  have hD0 := P.Delta0_nonneg e
  refine maxEntry_le_of _ _ (by exact_mod_cast h2) (fun r k ↦ ?_) (fun r ↦ ?_) (fun k ↦ ?_)
  · induction r using Fin.lastCases with
    | last =>
      induction k using Fin.lastCases with
      | last => rw [shieldLP_A_ll, abs_of_nonneg hD0]; linarith
      | cast k =>
        rw [shieldLP_A_lc]
        split_ifs
        · rw [abs_zero]; linarith
        · rw [abs_neg, abs_of_nonneg hcoef0]; nlinarith
    | cast i =>
      induction k using Fin.lastCases with
      | last => rw [shieldLP_A_cl, abs_zero]; linarith
      | cast k => rw [shieldLP_A_cc]; linarith [P.abs_canonical_A_le e i k]
  · induction r using Fin.lastCases with
    | last => rw [shieldLP_b_l, abs_one]; linarith
    | cast i => rw [shieldLP_b_c]; linarith [P.abs_canonical_b_le e i]
  · induction k using Fin.lastCases with
    | last => rw [shieldLP_c_l, abs_zero]; linarith
    | cast k => rw [shieldLP_c_c]; linarith [P.abs_canonical_c_le e k]

lemma weightedLP_maxEntry_le (hm : 1 ≤ m) :
    (P.weightedLP e σ).maxEntry ≤ (n + 1) * ((m + 1) * P.maxEntry) ^ (2 * m + 2) := by
  obtain ⟨h2, ha, hc, hb, hF⟩ := P.entry_bounds hm
  set T : ℤ := ((((m + 1) * P.maxEntry) ^ (2 * m + 2) : ℕ) : ℤ) with hT
  have hF0 : (0 : ℤ) ≤ P.detBd := Nat.cast_nonneg _
  have hm0 : (0 : ℤ) ≤ m := Nat.cast_nonneg _
  have hn0 : (0 : ℤ) ≤ n := Nat.cast_nonneg _
  have hT0 : 0 ≤ T := by linarith
  have hTn : T ≤ (n + 1) * T := by nlinarith
  have hW0 := (P.shieldCoeff_nonneg e).trans (P.shieldW_ge e)
  have hWle : P.shieldW e ≤ T := (P.shieldW_le e).trans ha
  have hrW : ∀ r : ℕ, r ≤ n + 1 → |(r : ℤ) * P.shieldW e| ≤ (n + 1) * T := by
    intro r hr
    rw [abs_mul, abs_of_nonneg hW0, Nat.abs_cast]
    exact mul_le_mul (by exact_mod_cast hr) hWle hW0 (by linarith)
  have hcoef := P.shieldCoeff_le e
  have hD := P.Delta0_le e
  have hD0 := P.Delta0_nonneg e
  have hN : ((((n + 1) * ((m + 1) * P.maxEntry) ^ (2 * m + 2) : ℕ)) : ℤ) = (n + 1) * T := by
    rw [hT]; push_cast; ring
  have h2' : 2 ≤ ((m + 1) * P.maxEntry) ^ (2 * m + 2) := by
    have h := h2; rw [hT] at h; exact_mod_cast h
  refine maxEntry_le_of _ _ (le_trans h2' (Nat.le_mul_of_pos_left _ (Nat.succ_pos n)))
    (fun r k ↦ ?_) (fun r ↦ ?_) (fun k ↦ ?_) <;> rw [hN]
  · induction r using Fin.lastCases with
    | last =>
      induction k using Fin.lastCases with
      | last => rw [weightedLP_A_ll]; exact hrW _ (by simp)
      | cast k =>
        rw [weightedLP_A_lc]
        split_ifs
        · rw [abs_zero]; linarith
        · rw [abs_neg]; exact hrW _ (by rw [shieldRank_castSucc]; have := (σ k).isLt; omega)
    | cast i =>
      induction k using Fin.lastCases with
      | last => rw [weightedLP_A_cl, abs_zero]; linarith
      | cast k =>
        rw [weightedLP_A_cc]
        split_ifs
        · exact hrW _ (by rw [shieldRank_castSucc]; have := (σ k).isLt; omega)
        · rw [abs_zero]; linarith
        · linarith [P.abs_canonical_A_le e i k]
  · induction r using Fin.lastCases with
    | last => rw [weightedLP_b, shieldLP_b_l, abs_one]; linarith
    | cast i => rw [weightedLP_b, shieldLP_b_c]; linarith [P.abs_canonical_b_le e i]
  · induction k using Fin.lastCases with
    | last => rw [weightedLP_c, shieldLP_c_l, abs_zero]; linarith
    | cast k => rw [weightedLP_c, shieldLP_c_c]; linarith [P.abs_canonical_c_le e k]

end IntLP

end WolfeSimplex

namespace WolfeSimplex

namespace IntLP

variable {m n : ℕ}

/-- Lemma 12 (`lem:shield-lp`) (statement `shield_lp` of `MainResults`). -/
theorem shield_lp_main (P : IntLP m n) (hP : P.IsAdmissible) (e : Fin m → Fin n)
    (hB₀ : P.toLP.IsFeasibleBasis (basisOf e)) :
    (P.shieldLP e).IsAdmissible ∧
    (P.shieldLP e).maxEntry ≤ ((m + 1) * P.maxEntry) ^ (2 * m + 2) ∧
    (∀ B' : Finset (Fin (n + 1)), (P.shieldLP e).toLP.IsFeasibleBasis B' ↔
      ∃ B, P.toLP.IsFeasibleBasis B ∧ B' = hat B) ∧
    (∀ B, P.toLP.IsBasis B → ∀ j : Fin n,
      (P.shieldLP e).toLP.reducedCost (hat B) (Fin.castSucc j) =
        P.Delta0 e * P.toLP.reducedCost B j) ∧
    (∀ B, P.toLP.IsFeasibleBasis B → ∀ j ∈ P.toLP.improving B, ∀ i' : Fin (n + 1),
      (P.shieldLP e).toLP.IsLeavingLabel (hat B) (Fin.castSucc j) i' ↔
        ∃ i, i' = Fin.castSucc i ∧ P.toLP.IsLeavingLabel B j i) := by
  have h := P.isShield e hB₀.1
  refine ⟨P.shieldLP_isAdmissible e hP hB₀, P.shieldLP_maxEntry_le e hP.1, h.isFeasibleBasis_iff,
    fun B hB j ↦ ?_, fun B hB j hj i' ↦ h.isLeavingLabel_hat_iff hP.2.2.1 hB hj i'⟩
  rw [h.reducedCost_hat hB]
  simp

/-- Lemma 16 (`lem:weighted`)(a) (statement `weighted_a` of `MainResults`). -/
theorem weighted_a_main (P : IntLP m n) (hP : P.IsAdmissible) (e : Fin m → Fin n)
    (hB₀ : P.toLP.IsFeasibleBasis (basisOf e)) (σ : Equiv.Perm (Fin n)) :
    (P.weightedLP e σ).IsAdmissible ∧
    (P.weightedLP e σ).maxEntry ≤ (n + 1) * ((m + 1) * P.maxEntry) ^ (2 * m + 2) ∧
    (∀ B' : Finset (Fin (n + 1)), (P.weightedLP e σ).toLP.IsFeasibleBasis B' ↔
      ∃ B, P.toLP.IsFeasibleBasis B ∧ B' = hat B) ∧
    (∀ B, P.toLP.IsFeasibleBasis B →
      (P.weightedLP e σ).toLP.improving (hat B) = (P.toLP.improving B).map Fin.castSuccEmb) ∧
    (∀ B, P.toLP.IsFeasibleBasis B → ∀ j ∈ P.toLP.improving B, ∀ i' : Fin (n + 1),
      (P.weightedLP e σ).toLP.IsLeavingLabel (hat B) (Fin.castSucc j) i' ↔
        ∃ i, i' = Fin.castSucc i ∧ P.toLP.IsLeavingLabel B j i) := by
  have h := P.isShieldW e σ hB₀.1
  have hκ : (0 : ℝ) < P.Delta0 e := by exact_mod_cast P.Delta0_pos e hB₀.1
  exact ⟨P.weightedLP_isAdmissible e hP hB₀ σ, P.weightedLP_maxEntry_le e σ hP.1,
    h.isFeasibleBasis_iff, fun B hB ↦ h.improving_hat hκ hB.1,
    fun B hB j hj i' ↦ h.isLeavingLabel_hat_iff hP.2.2.1 hB hj i'⟩

end IntLP

end WolfeSimplex
