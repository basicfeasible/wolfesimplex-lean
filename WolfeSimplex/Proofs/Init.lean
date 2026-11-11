import WolfeSimplex.Proofs.Shield

/-!
# Starting at the minimum-norm atom (paper: Lemma 13 (`lem:init`), Lemma 16 (`lem:weighted`)(b),(c))

Proofs of `init_a`, `init_b`, `init_c`, `weighted_b`, `weighted_c` of `MainResults`
(here named `init_a_main`, …).

* Generic part (`section Diag`): an LP `Q` with `M` rows in which the column of the
  label `E r` is `d_r e_r` (`d_r ≥ 1`), with cost `0` and `b > 0`. For a support
  `S ∋ slack` inside `{E r} ∪ {slack}`, `S` is a corral with affine minimizer
  `w_R = (N C, -N² β_R)` (`R` = rows whose label is not in `S`, `β = b/T`), the
  gaps are `g_k(w_R) = N² C c_k - N⁴ (∑_{i∈R} A_{ik} b_i)/T`, and a label with
  `∑_{i∈R} A_{ik} b_i ≤ -1` has positive gap.
* Norms (`normSq_lt_of_nu`): for `M ≥ 2` rows, `‖A_j‖² + 1 ≤ ‖A_{j'}‖²` implies
  `‖p_j‖ < ‖p_{j'}‖` (the slack column counts as `0`).
* Both (LP⁺) (`d_r = Δ₀`) and (LP̃⁺) (`d_r = r(ℓ) W`) are instances.

Only the elementary bound `2 ∑_r |b_r| < T` is used instead of Lemma 8 (`lem:T-bound`)
(it gives `∑ β_ℓ/d_ℓ < 1/2` as well, since `d_ℓ ≥ 1`).
-/

namespace WolfeSimplex.IntLP

open Finset Matrix Wolfe

section Generic

variable {M L : ℕ} (Q : IntLP M L)

lemma abs_c_le_C_sub_one (k : Fin L) : |(Q.c k : ℝ)| ≤ (Q.C : ℝ) - 1 := by
  have h := Q.natAbs_c_le k
  have h2 : |Q.c k| ≤ Q.C - 1 := by
    rw [Int.abs_eq_natAbs]; unfold C; omega
  exact_mod_cast h2

lemma one_le_C : (1 : ℝ) ≤ Q.C := by
  have : (1 : ℤ) ≤ Q.C := by unfold C; omega
  exact_mod_cast this

lemma C_le_K : (Q.C : ℝ) ≤ Q.K := by
  have h := Q.natAbs_gamma_le (Fin.last L)
  rw [gamma_last] at h
  have : Q.C ≤ (Q.K : ℤ) := by
    have h1 : (1 : ℤ) ≤ Q.C := by unfold C; omega
    omega
  exact_mod_cast this

lemma K_le_H : Q.K ≤ Q.H := by
  have hK := Q.one_le_K
  unfold H
  calc Q.K ≤ Q.K ^ 2 := Nat.le_self_pow (by norm_num) _
    _ ≤ (M + 1) * Q.K ^ 2 := Nat.le_mul_of_pos_left _ (by omega)
    _ ≤ ((M + 1) * Q.K ^ 2) ^ (M + 1) := Nat.le_self_pow (by omega) _

lemma four_T_K_sq_le_N_sq (hM : 1 ≤ M) : 4 * Q.T * Q.K ^ 2 ≤ Q.N ^ 2 := by
  have hK := Q.one_le_K
  have hT := Q.one_le_T
  have hH := Q.K_le_H
  have h1 : Q.K ≤ Q.H ^ 3 := le_trans hH (Nat.le_self_pow (by norm_num) _)
  have h2 : 2 * Q.T * Q.K ≤ Q.N := by
    unfold N
    calc 2 * Q.T * Q.K ≤ 2 * Q.T * Q.H ^ 3 := by gcongr
      _ ≤ 2 * M * Q.T * Q.H ^ 3 := by
        have : 2 * Q.T * Q.H ^ 3 * 1 ≤ 2 * Q.T * Q.H ^ 3 * M := Nat.mul_le_mul_left _ hM
        calc 2 * Q.T * Q.H ^ 3 = 2 * Q.T * Q.H ^ 3 * 1 := by ring
          _ ≤ 2 * Q.T * Q.H ^ 3 * M := this
          _ = 2 * M * Q.T * Q.H ^ 3 := by ring
  have h3 : 2 * Q.K ≤ Q.N := le_trans (by nlinarith) h2
  nlinarith

lemma two_sum_abs_b_lt (hM : 1 ≤ M) : 2 * ∑ r, |(Q.b r : ℝ)| < Q.T := by
  have hU := Q.one_le_U
  have h1 : ∑ r, |(Q.b r : ℝ)| ≤ M * (Q.U : ℝ) := by
    calc ∑ r, |(Q.b r : ℝ)| ≤ ∑ _r : Fin M, (Q.U : ℝ) :=
          Finset.sum_le_sum fun r _ ↦ by exact_mod_cast Q.abs_b_le r
      _ = M * (Q.U : ℝ) := by simp
  have h2 : 2 * M * Q.U < Q.T := by
    unfold T
    have : M * Q.U ≤ (M * Q.U) ^ M := Nat.le_self_pow (by omega) _
    have : Q.U ≤ M * Q.U := Nat.le_mul_of_pos_left _ (by omega)
    nlinarith
  have h3 : (2 * M * Q.U : ℝ) < Q.T := by exact_mod_cast h2
  linarith

lemma eight_M_U_sq_lt (hM : 2 ≤ M) : 8 * M * Q.U ^ 2 < Q.T := by
  have hU := Q.one_le_U
  unfold T
  have h1 : (M * Q.U) ^ 2 ≤ (M * Q.U) ^ M :=
    Nat.pow_le_pow_right (Nat.mul_pos (by omega) (by omega)) hM
  have h2 : 4 * Q.U ^ 2 ≤ (M * Q.U) ^ 2 := by
    rw [mul_pow]
    have : 4 ≤ M ^ 2 := by nlinarith
    exact Nat.mul_le_mul_right _ this
  nlinarith

/-- The point `(N C, -N² β_R)`. -/
noncomputable def wR (R : Finset (Fin M)) : Fin (M + 1) → ℝ :=
  Fin.cons (α := fun _ ↦ ℝ) ((Q.N : ℝ) * Q.C)
    (fun i ↦ -((Q.N : ℝ) ^ 2 * (if i ∈ R then (Q.b i : ℝ) / Q.T else 0)))

lemma sum_mul_ite_mem (R : Finset (Fin M)) (f g : Fin M → ℝ) :
    ∑ i, f i * (if i ∈ R then g i else 0) = ∑ i ∈ R, f i * g i := by
  simp [mul_ite, Finset.sum_ite_mem]

lemma normSq_wR (R : Finset (Fin M)) :
    normSq (Q.wR R) = (Q.N : ℝ) ^ 2 * Q.C ^ 2 +
      (Q.N : ℝ) ^ 4 * ∑ i ∈ R, ((Q.b i : ℝ) / Q.T) ^ 2 := by
  simp only [normSq, dotProduct, Fin.sum_univ_succ, wR, Fin.cons_zero, Fin.cons_succ]
  have : ∑ i : Fin M, -((Q.N : ℝ) ^ 2 * (if i ∈ R then (Q.b i : ℝ) / Q.T else 0)) *
      -((Q.N : ℝ) ^ 2 * (if i ∈ R then (Q.b i : ℝ) / Q.T else 0)) =
      ∑ i, (Q.N : ℝ) ^ 4 * (if i ∈ R then ((Q.b i : ℝ) / Q.T) ^ 2 else 0) := by
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    split_ifs <;> ring
  rw [this, ← Finset.mul_sum, ← Finset.sum_filter]
  simp
  ring

lemma gap_wR_castSucc (R : Finset (Fin M)) (k : Fin L) :
    gap Q.atom (Fin.castSucc k) (Q.wR R) = (Q.N : ℝ) ^ 2 * Q.C * Q.c k -
      (Q.N : ℝ) ^ 4 * (∑ i ∈ R, (Q.A i k : ℝ) * Q.b i) / Q.T := by
  have hT : (Q.T : ℝ) ≠ 0 := Q.T_pos.ne'
  rw [gap, normSq_wR]
  simp only [dotProduct, Fin.sum_univ_succ, atom, wR, Fin.cons_zero, Fin.cons_succ,
    alpha_castSucc, gamma_castSucc]
  have : ∑ i : Fin M, (Q.N : ℝ) ^ 2 * ((Q.A i k : ℝ) - (Q.b i : ℝ) / Q.T) *
      -((Q.N : ℝ) ^ 2 * (if i ∈ R then (Q.b i : ℝ) / Q.T else 0)) =
      ∑ i, (-(Q.N : ℝ) ^ 4 * ((Q.A i k : ℝ) - (Q.b i : ℝ) / Q.T)) *
        (if i ∈ R then (Q.b i : ℝ) / Q.T else 0) := by
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    ring
  rw [this, sum_mul_ite_mem]
  have e1 : ∑ i ∈ R, (-(Q.N : ℝ) ^ 4 * ((Q.A i k : ℝ) - (Q.b i : ℝ) / Q.T)) * ((Q.b i : ℝ) / Q.T)
      = -(Q.N : ℝ) ^ 4 * (∑ i ∈ R, (Q.A i k : ℝ) * Q.b i) / Q.T +
        (Q.N : ℝ) ^ 4 * ∑ i ∈ R, ((Q.b i : ℝ) / Q.T) ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    field_simp
    ring
  rw [e1]
  push_cast
  ring

lemma gap_wR_last (R : Finset (Fin M)) :
    gap Q.atom (Fin.last L) (Q.wR R) = 0 := by
  rw [gap, normSq_wR]
  simp only [dotProduct, Fin.sum_univ_succ, atom, wR, Fin.cons_zero, Fin.cons_succ,
    alpha_last, gamma_last]
  have : ∑ i : Fin M, (Q.N : ℝ) ^ 2 * (-(Q.b i : ℝ) / Q.T) *
      -((Q.N : ℝ) ^ 2 * (if i ∈ R then (Q.b i : ℝ) / Q.T else 0)) =
      ∑ i, (Q.N : ℝ) ^ 4 * (if i ∈ R then ((Q.b i : ℝ) / Q.T) ^ 2 else 0) := by
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    split_ifs <;> ring
  rw [this, ← Finset.mul_sum, ← Finset.sum_filter]
  simp
  ring


/-! ### LPs whose columns `E r` are `d_r e_r` -/

section Diag

variable {E : Fin M → Fin L} (hE : Function.Injective E)

/-- The rows `r` whose label `E r` is in `S`. -/
def rowsIn (E : Fin M → Fin L) (S : Finset (Fin (L + 1))) : Finset (Fin M) :=
  univ.filter fun r ↦ Fin.castSucc (E r) ∈ S

/-- The rows `r` whose label `E r` is not in `S` (the set `R`). -/
def rowsOut (E : Fin M → Fin L) (S : Finset (Fin (L + 1))) : Finset (Fin M) :=
  univ.filter fun r ↦ Fin.castSucc (E r) ∉ S

include hE in
lemma castSucc_E_injective : Function.Injective fun r ↦ Fin.castSucc (E r) :=
  fun _ _ h ↦ hE (Fin.castSucc_injective _ h)

include hE in
lemma sum_over_S {X : Type*} [AddCommMonoid X] {S : Finset (Fin (L + 1))}
    (hS : Fin.last L ∈ S) (hSB : S ⊆ hat (univ.image E)) (f : Fin (L + 1) → X) :
    ∑ j ∈ S, f j = f (Fin.last L) + ∑ r ∈ rowsIn E S, f (Fin.castSucc (E r)) := by
  classical
  have hSeq : S = insert (Fin.last L) ((rowsIn E S).map
      ⟨fun r ↦ Fin.castSucc (E r), castSucc_E_injective hE⟩) := by
    ext j
    simp only [mem_insert, mem_map, Function.Embedding.coeFn_mk, rowsIn, mem_filter, mem_univ,
      true_and]
    constructor
    · intro hj
      by_cases hl : j = Fin.last L
      · exact Or.inl hl
      · right
        have := hSB hj
        simp only [hat, mem_insert, hl, false_or, mem_map, mem_image, mem_univ, true_and,
          Fin.castSuccEmb_apply] at this
        obtain ⟨k, ⟨r, rfl⟩, rfl⟩ := this
        exact ⟨r, hj, rfl⟩
    · rintro (rfl | ⟨r, hr, rfl⟩)
      · exact hS
      · exact hr
  conv_lhs => rw [hSeq]
  rw [sum_insert, sum_map]
  · rfl
  · simp [Fin.castSucc_ne_last]


lemma mem_hat_image {j : Fin (L + 1)} (hj : j ∈ hat (univ.image E)) :
    j = Fin.last L ∨ ∃ r, j = Fin.castSucc (E r) := by
  simp only [hat, mem_insert, mem_map, mem_image, mem_univ, true_and,
    Fin.castSuccEmb_apply] at hj
  rcases hj with h | ⟨k, ⟨r, rfl⟩, rfl⟩
  · exact Or.inl h
  · exact Or.inr ⟨r, rfl⟩

lemma comb_zero (hc : ∀ r, Q.c (E r) = 0) {S : Finset (Fin (L + 1))}
    (hSB : S ⊆ hat (univ.image E)) (μ : Fin (L + 1) → ℝ) :
    (∑ j ∈ S, μ j • Q.atom j) 0 = (Q.N : ℝ) * Q.C * ∑ j ∈ S, μ j := by
  rw [Finset.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [Pi.smul_apply, atom_zero, smul_eq_mul]
  rcases mem_hat_image (hSB hj) with rfl | ⟨r, rfl⟩
  · rw [gamma_last]; ring
  · rw [gamma_castSucc, hc r]; push_cast; ring

include hE in
lemma comb_succ {d : Fin M → ℤ} (hA : ∀ r r', Q.A r (E r') = if r = r' then d r' else 0)
    {S : Finset (Fin (L + 1))} (hS : Fin.last L ∈ S) (hSB : S ⊆ hat (univ.image E))
    (μ : Fin (L + 1) → ℝ) (i : Fin M) :
    (∑ j ∈ S, μ j • Q.atom j) i.succ = (Q.N : ℝ) ^ 2 * (-((Q.b i : ℝ) / Q.T) * ∑ j ∈ S, μ j +
      if i ∈ rowsIn E S then μ (Fin.castSucc (E i)) * d i else 0) := by
  rw [Finset.sum_apply, sum_over_S hE hS hSB, sum_over_S hE hS hSB]
  simp only [Pi.smul_apply, atom_succ, smul_eq_mul, alpha_last, alpha_castSucc, hA]
  have h1 : ∑ r ∈ rowsIn E S, μ (Fin.castSucc (E r)) * ((Q.N : ℝ) ^ 2 *
      (((if i = r then d r else 0 : ℤ) : ℝ) - (Q.b i : ℝ) / Q.T)) =
      (Q.N : ℝ) ^ 2 * ∑ r ∈ rowsIn E S, (if i = r then μ (Fin.castSucc (E r)) * d r else 0) -
      (Q.N : ℝ) ^ 2 * ((Q.b i : ℝ) / Q.T) * ∑ r ∈ rowsIn E S, μ (Fin.castSucc (E r)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    split_ifs <;> push_cast <;> ring
  rw [h1, Finset.sum_ite_eq]
  ring


omit Q in
lemma mem_rowsOut {S : Finset (Fin (L + 1))} {r : Fin M} :
    r ∈ rowsOut E S ↔ r ∉ rowsIn E S := by
  simp [rowsOut, rowsIn]

variable (E) in
/-- The affine coefficients of `S`: `β_r/d_r` on the label `E r ∈ S`, the rest on the
slack label. -/
noncomputable def lamS (d : Fin M → ℤ) (S : Finset (Fin (L + 1))) : Fin (L + 1) → ℝ :=
  fun j ↦ if j = Fin.last L then 1 - ∑ r ∈ rowsIn E S, (Q.b r : ℝ) / Q.T / d r
    else ∑ r ∈ rowsIn E S, if j = Fin.castSucc (E r) then (Q.b r : ℝ) / Q.T / d r else 0

lemma lamS_last (d : Fin M → ℤ) (S : Finset (Fin (L + 1))) :
    Q.lamS E d S (Fin.last L) = 1 - ∑ r ∈ rowsIn E S, (Q.b r : ℝ) / Q.T / d r := by
  simp [lamS]

include hE in
lemma lamS_castSucc (d : Fin M → ℤ) (S : Finset (Fin (L + 1))) (r : Fin M) :
    Q.lamS E d S (Fin.castSucc (E r)) =
      if r ∈ rowsIn E S then (Q.b r : ℝ) / Q.T / d r else 0 := by
  simp only [lamS, Fin.castSucc_ne_last, ite_false, Fin.castSucc_inj, hE.eq_iff]
  rw [Finset.sum_ite_eq]

lemma lamS_out (d : Fin M → ℤ) {S : Finset (Fin (L + 1))} (hS : Fin.last L ∈ S)
    {j : Fin (L + 1)} (hj : j ∉ S) : Q.lamS E d S j = 0 := by
  have hjl : j ≠ Fin.last L := fun h ↦ hj (h ▸ hS)
  simp only [lamS, hjl, ite_false]
  refine Finset.sum_eq_zero fun r hr ↦ ?_
  rw [ite_eq_right]
  rintro rfl
  exact hj (by simpa [rowsIn] using hr)

include hE in
lemma sum_lamS (d : Fin M → ℤ) {S : Finset (Fin (L + 1))} (hS : Fin.last L ∈ S)
    (hSB : S ⊆ hat (univ.image E)) : ∑ j ∈ S, Q.lamS E d S j = 1 := by
  rw [sum_over_S hE hS hSB, lamS_last]
  have : ∑ r ∈ rowsIn E S, Q.lamS E d S (Fin.castSucc (E r)) =
      ∑ r ∈ rowsIn E S, (Q.b r : ℝ) / Q.T / d r :=
    Finset.sum_congr rfl fun r hr ↦ by rw [Q.lamS_castSucc hE d S r, ite_eq_left hr]
  rw [this]
  ring

include hE in
lemma comb_lamS (hc : ∀ r, Q.c (E r) = 0) {d : Fin M → ℤ} (hd : ∀ r, 1 ≤ d r)
    (hA : ∀ r r', Q.A r (E r') = if r = r' then d r' else 0)
    {S : Finset (Fin (L + 1))} (hS : Fin.last L ∈ S) (hSB : S ⊆ hat (univ.image E)) :
    ∑ j ∈ S, Q.lamS E d S j • Q.atom j = Q.wR (rowsOut E S) := by
  funext t
  induction t using Fin.cases with
  | zero => rw [comb_zero Q hc hSB, sum_lamS Q hE d hS hSB]; simp [wR]
  | succ i =>
    rw [comb_succ Q hE hA hS hSB, sum_lamS Q hE d hS hSB, lamS_castSucc Q hE]
    simp only [wR, Fin.cons_succ, mem_rowsOut]
    have hdi : (d i : ℝ) ≠ 0 := by have := hd i; positivity
    by_cases hi : i ∈ rowsIn E S
    · simp only [hi, ite_true, not_true_eq_false, ite_false]
      field_simp
      ring
    · simp only [hi, ite_false, not_false_eq_true, ite_true]
      ring

include hE in
lemma affIndep_S {d : Fin M → ℤ} (hd : ∀ r, 1 ≤ d r)
    (hA : ∀ r r', Q.A r (E r') = if r = r' then d r' else 0) (hM : 1 ≤ M)
    {S : Finset (Fin (L + 1))} (hS : Fin.last L ∈ S) (hSB : S ⊆ hat (univ.image E)) :
    IsAffinelyIndependent Q.atom S := by
  intro μ hcomb hsum
  have hN : (Q.N : ℝ) ≠ 0 := (Q.N_pos' hM).ne'
  have hE0 : ∀ r ∈ rowsIn E S, μ (Fin.castSucc (E r)) = 0 := by
    intro r hr
    have h := congrFun hcomb r.succ
    rw [comb_succ Q hE hA hS hSB, hsum, ite_eq_left hr] at h
    have hdi : (d r : ℝ) ≠ 0 := by have := hd r; positivity
    simp only [Pi.zero_apply, mul_zero, zero_add, mul_eq_zero, hN, hdi, false_or,
      or_false, pow_eq_zero_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true] at h
    exact h
  have hlast : μ (Fin.last L) = 0 := by
    rw [sum_over_S hE hS hSB, Finset.sum_eq_zero hE0, add_zero] at hsum
    exact hsum
  intro j hj
  rcases mem_hat_image (hSB hj) with rfl | ⟨r, rfl⟩
  · exact hlast
  · exact hE0 r (by simp [rowsIn, hj])

lemma sum_beta_div_lt (hM : 1 ≤ M) {d : Fin M → ℤ} (hd : ∀ r, 1 ≤ d r)
    (hb : ∀ r, 0 < Q.b r) (s : Finset (Fin M)) :
    ∑ r ∈ s, (Q.b r : ℝ) / Q.T / d r < 1 / 2 := by
  have hT := Q.T_pos
  have h2 := Q.two_sum_abs_b_lt hM
  have h3 : ∑ r ∈ s, (Q.b r : ℝ) / Q.T / d r ≤ ∑ r, |(Q.b r : ℝ)| / Q.T := by
    calc ∑ r ∈ s, (Q.b r : ℝ) / Q.T / d r ≤ ∑ r ∈ s, |(Q.b r : ℝ)| / Q.T := by
          refine Finset.sum_le_sum fun r _ ↦ ?_
          have hbr : (0 : ℝ) < Q.b r := by exact_mod_cast hb r
          have hdr : (1 : ℝ) ≤ d r := by exact_mod_cast hd r
          rw [abs_of_pos hbr, div_le_iff₀ (by linarith)]
          have : 0 ≤ (Q.b r : ℝ) / Q.T := by positivity
          nlinarith
      _ ≤ ∑ r, |(Q.b r : ℝ)| / Q.T :=
          Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ ↦ by positivity
  rw [← Finset.sum_div] at h3
  have h4 : (∑ r, |(Q.b r : ℝ)|) / Q.T < 1 / 2 := by
    rw [div_lt_iff₀ hT]; linarith
  linarith

include hE in
/-- Generic part (a): `S` is a corral with affine minimizer `w_R` and coefficients
`lamS`. -/
lemma diag_corral (hc : ∀ r, Q.c (E r) = 0) {d : Fin M → ℤ} (hd : ∀ r, 1 ≤ d r)
    (hA : ∀ r r', Q.A r (E r') = if r = r' then d r' else 0) (hb : ∀ r, 0 < Q.b r)
    (hM : 1 ≤ M)
    {S : Finset (Fin (L + 1))} (hS : Fin.last L ∈ S) (hSB : S ⊆ hat (univ.image E)) :
    IsCorral Q.atom S ∧ affineMin Q.atom S = Q.wR (rowsOut E S) ∧
      affineCoeffs Q.atom S = Q.lamS E d S := by
  have hmem : Q.wR (rowsOut E S) ∈ affineHull Q.atom S :=
    ⟨Q.lamS E d S, sum_lamS Q hE d hS hSB, (comb_lamS Q hE hc hd hA hS hSB).symm⟩
  have hmin : affineMin Q.atom S = Q.wR (rowsOut E S) := by
    apply affineMin_eq_of_gap_zero _ hmem
    intro j hj
    rcases mem_hat_image (hSB hj) with rfl | ⟨r, rfl⟩
    · exact Q.gap_wR_last _
    · rw [gap_wR_castSucc, hc r]
      have hr : r ∉ rowsOut E S := by simp [rowsOut, hj]
      have : ∑ i ∈ rowsOut E S, (Q.A i (E r) : ℝ) * Q.b i = 0 := by
        refine Finset.sum_eq_zero fun i hi ↦ ?_
        rw [hA, ite_eq_right (fun (h : i = r) ↦ hr (h ▸ hi))]; simp
      rw [this]; simp
  have hind := affIndep_S Q hE hd hA hM hS hSB
  have hcoef : affineCoeffs Q.atom S = Q.lamS E d S :=
    affineCoeffs_eq_of _ hind (fun j hj ↦ lamS_out Q d hS hj) (sum_lamS Q hE d hS hSB)
      (by rw [hmin]; exact comb_lamS Q hE hc hd hA hS hSB)
  refine ⟨⟨⟨_, hS⟩, hind, fun j hj ↦ ?_⟩, hmin, hcoef⟩
  rw [hcoef]
  rcases mem_hat_image (hSB hj) with rfl | ⟨r, rfl⟩
  · rw [lamS_last]
    linarith [Q.sum_beta_div_lt hM hd hb (rowsIn E S)]
  · have hr : r ∈ rowsIn E S := by simp [rowsIn, hj]
    rw [lamS_castSucc Q hE, ite_eq_left hr]
    have hbr : (0 : ℝ) < Q.b r := by exact_mod_cast hb r
    have hdr : (0 : ℝ) < d r := by have := hd r; exact_mod_cast (by omega : (0 : ℤ) < d r)
    have := Q.T_pos
    positivity


lemma gap_wR_E {d : Fin M → ℤ} (hc : ∀ r, Q.c (E r) = 0)
    (hA : ∀ r r', Q.A r (E r') = if r = r' then d r' else 0) (R : Finset (Fin M)) (r : Fin M) :
    gap Q.atom (Fin.castSucc (E r)) (Q.wR R) =
      if r ∈ R then -(Q.N : ℝ) ^ 4 * d r * ((Q.b r : ℝ) / Q.T) else 0 := by
  rw [gap_wR_castSucc, hc r]
  simp only [hA]
  have : ∑ i ∈ R, (((if i = r then d r else 0 : ℤ) : ℝ)) * (Q.b i : ℝ) =
      ∑ i ∈ R, (if i = r then (d r : ℝ) * Q.b r else 0) :=
    Finset.sum_congr rfl fun i _ ↦ by split_ifs with h <;> simp [h]
  rw [this, Finset.sum_ite_eq']
  split_ifs <;> ring

lemma gap_pos_of (hM : 1 ≤ M) (R : Finset (Fin M)) (k : Fin L)
    (h : ∑ i ∈ R, Q.A i k * Q.b i ≤ -1) : 0 < gap Q.atom (Fin.castSucc k) (Q.wR R) := by
  rw [gap_wR_castSucc]
  have hX : (∑ i ∈ R, (Q.A i k : ℝ) * Q.b i) ≤ -1 := by exact_mod_cast h
  have hT := Q.T_pos
  have hN := Q.N_pos' hM
  have hC := Q.one_le_C
  have hCK := Q.C_le_K
  have hc := Q.abs_c_le_C_sub_one k
  have hNK : (4 * Q.T * Q.K ^ 2 : ℝ) ≤ (Q.N : ℝ) ^ 2 := by
    exact_mod_cast Q.four_T_K_sq_le_N_sq hM
  set a : ℝ := (Q.N : ℝ) ^ 2 with ha
  have ha0 : 0 < a := by positivity
  have h4 : (Q.N : ℝ) ^ 4 = a * a := by rw [ha]; ring
  rw [h4]
  have hcl : -(Q.C : ℝ) * ((Q.C : ℝ) - 1) ≤ (Q.C : ℝ) * Q.c k := by
    have := neg_abs_le (Q.c k : ℝ)
    nlinarith
  set X := ∑ i ∈ R, (Q.A i k : ℝ) * Q.b i
  have hp : 0 < a * (a / Q.T) := by positivity
  have h5 : a * a * X / Q.T ≤ -(a * (a / Q.T)) := by
    calc a * a * X / Q.T = a * (a / Q.T) * X := by ring
      _ ≤ a * (a / Q.T) * (-1) := mul_le_mul_of_nonneg_left hX hp.le
      _ = -(a * (a / Q.T)) := by ring
  have hCK2 : (Q.C : ℝ) ^ 2 ≤ (Q.K : ℝ) ^ 2 := pow_le_pow_left₀ (by linarith) hCK 2
  have h6 : 4 * (Q.C : ℝ) ^ 2 ≤ a / Q.T := by
    rw [le_div_iff₀ hT]; nlinarith
  have h7 : a * (4 * (Q.C : ℝ) ^ 2) ≤ a * (a / Q.T) := mul_le_mul_of_nonneg_left h6 ha0.le
  have h8 : a * (-(Q.C : ℝ) * ((Q.C : ℝ) - 1)) ≤ a * ((Q.C : ℝ) * Q.c k) :=
    mul_le_mul_of_nonneg_left hcl ha0.le
  have h9 : 0 < a * (Q.C : ℝ) * (3 * Q.C + 1) := by positivity
  nlinarith

include hE in
lemma diag_improving (hc : ∀ r, Q.c (E r) = 0) {d : Fin M → ℤ} (hd : ∀ r, 1 ≤ d r)
    (hA : ∀ r r', Q.A r (E r') = if r = r' then d r' else 0) (hb : ∀ r, 0 < Q.b r)
    (hM : 1 ≤ M)
    {S : Finset (Fin (L + 1))} (hS : Fin.last L ∈ S) (hSB : S ⊆ hat (univ.image E))
    (hneg : ∀ k, k ∉ univ.image E → ∑ i ∈ rowsOut E S, Q.A i k * Q.b i ≤ -1) :
    improving Q.atom (affineMin Q.atom S) = (univ.image E).map Fin.castSuccEmb \ S := by
  rw [(diag_corral Q hE hc hd hA hb hM hS hSB).2.1]
  ext j
  simp only [improving, mem_filter, mem_univ, true_and, mem_sdiff, mem_map, mem_image,
    Fin.castSuccEmb_apply]
  induction j using Fin.lastCases with
  | last =>
    rw [gap_wR_last]
    simp [Fin.castSucc_ne_last]
  | cast k =>
    by_cases hk : k ∈ univ.image E
    · obtain ⟨r, -, rfl⟩ := mem_image.1 hk
      rw [gap_wR_E Q hc hA]
      have hbr : (0 : ℝ) < Q.b r := by exact_mod_cast hb r
      have hdr : (0 : ℝ) < d r := by exact_mod_cast (by have := hd r; omega : (0 : ℤ) < d r)
      have hN := Q.N_pos' hM
      have hT := Q.T_pos
      by_cases hr : r ∈ rowsOut E S
      · rw [ite_eq_left hr]
        have hrS : Fin.castSucc (E r) ∉ S := by simpa [rowsOut] using hr
        simp only [hrS, not_false_eq_true, and_true]
        constructor
        · intro _; exact ⟨E r, ⟨r, rfl⟩, rfl⟩
        · intro _
          have : 0 < (Q.N : ℝ) ^ 4 * d r * ((Q.b r : ℝ) / Q.T) := by positivity
          linarith
      · rw [ite_eq_right hr]
        have hrS : Fin.castSucc (E r) ∈ S := by simpa [rowsOut] using hr
        simp [hrS]
    · have := Q.gap_pos_of hM (rowsOut E S) k (hneg k hk)
      constructor
      · intro h; linarith
      · rintro ⟨⟨k', ⟨r, rfl⟩, hk'⟩, -⟩
        exact absurd (mem_image.2 ⟨r, mem_univ _, Fin.castSucc_injective _ hk'⟩) hk

include hE in
lemma diag_major (hc : ∀ r, Q.c (E r) = 0) {d : Fin M → ℤ} (hd : ∀ r, 1 ≤ d r)
    (hA : ∀ r r', Q.A r (E r') = if r = r' then d r' else 0) (hb : ∀ r, 0 < Q.b r)
    (hM : 1 ≤ M)
    {S : Finset (Fin (L + 1))} (hS : Fin.last L ∈ S) (hSB : S ⊆ hat (univ.image E))
    (hneg : ∀ k, k ∉ univ.image E → ∑ i ∈ rowsOut E S, Q.A i k * Q.b i ≤ -1) :
    ∀ ℓ ∈ improving Q.atom (affineMin Q.atom S),
      ∀ S', MajorCycle Q.atom S ℓ S' ↔ S' = insert ℓ S := by
  intro ℓ hℓ S'
  have hℓ' := hℓ
  rw [diag_improving Q hE hc hd hA hb hM hS hSB hneg] at hℓ'
  have hsub : insert ℓ S ⊆ hat (univ.image E) := by
    refine insert_subset ?_ hSB
    exact mem_insert_of_mem (mem_sdiff.1 hℓ').1
  have hcor' := (diag_corral Q hE hc hd hA hb hM (mem_insert_of_mem hS) hsub).1
  have hcor := (diag_corral Q hE hc hd hA hb hM hS hSB).1
  constructor
  · rintro ⟨-, -, lam', hrt, -⟩
    have := eq_of_reflTransGen_of_corral Q.atom (s := ⟨insert ℓ S, affineCoeffs Q.atom S⟩)
      hcor' hrt
    simp only [State.mk.injEq] at this
    exact this.1
  · rintro rfl
    exact ⟨hcor, hℓ, affineCoeffs Q.atom S, Relation.ReflTransGen.refl, hcor'⟩

end Diag


/-! ### Norms of the atoms -/

/-- Column `j` of `A`, with the zero column for the slack label. -/
noncomputable def colR (j : Fin (L + 1)) (r : Fin M) : ℝ :=
  Fin.snoc (α := fun _ ↦ ℝ) (fun k ↦ (Q.A r k : ℝ)) 0 j

/-- `ν_j = ‖A_j‖²` (with `ν = 0` for the slack label). -/
def nu : Fin (L + 1) → ℤ := Fin.snoc (α := fun _ ↦ ℤ) (fun k ↦ ∑ r, Q.A r k ^ 2) 0

lemma alpha_eq_colR (j : Fin (L + 1)) (r : Fin M) :
    Q.alpha j r = Q.colR j r - (Q.b r : ℝ) / Q.T := by
  induction j using Fin.lastCases with
  | last => simp [colR]; ring
  | cast k => simp [colR]

lemma nu_eq (j : Fin (L + 1)) : (Q.nu j : ℝ) = ∑ r, Q.colR j r ^ 2 := by
  induction j using Fin.lastCases with
  | last => simp [nu, colR]
  | cast k => simp [nu, colR]

lemma abs_colR_le (j : Fin (L + 1)) (r : Fin M) : |Q.colR j r| ≤ Q.U := by
  induction j using Fin.lastCases with
  | last => simp [colR]
  | cast k => simp only [colR, Fin.snoc_castSucc]; exact_mod_cast Q.abs_A_le r k

lemma normSq_atom (j : Fin (L + 1)) :
    normSq (Q.atom j) = (Q.N : ℝ) ^ 2 * (Q.gamma j : ℝ) ^ 2 +
      (Q.N : ℝ) ^ 4 * (Q.nu j - 2 * ∑ r, Q.colR j r * ((Q.b r : ℝ) / Q.T) +
        ∑ r, ((Q.b r : ℝ) / Q.T) ^ 2) := by
  simp only [normSq, dotProduct, Fin.sum_univ_succ, atom, Fin.cons_zero, Fin.cons_succ,
    alpha_eq_colR, nu_eq]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  · ring
  · exact Finset.sum_congr rfl fun r _ ↦ by ring

lemma abs_colR_beta_le (hM : 2 ≤ M) (j : Fin (L + 1)) :
    |∑ r, Q.colR j r * ((Q.b r : ℝ) / Q.T)| ≤ 1 / 8 := by
  have hT := Q.T_pos
  have hU : (1 : ℝ) ≤ Q.U := by exact_mod_cast Q.one_le_U
  have h8 : (8 * M * Q.U ^ 2 : ℝ) < Q.T := by exact_mod_cast Q.eight_M_U_sq_lt hM
  calc |∑ r, Q.colR j r * ((Q.b r : ℝ) / Q.T)|
      ≤ ∑ r, |Q.colR j r * ((Q.b r : ℝ) / Q.T)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r : Fin M, (Q.U : ℝ) * (Q.U / Q.T) := by
        refine Finset.sum_le_sum fun r _ ↦ ?_
        rw [abs_mul, abs_div, abs_of_pos hT]
        have hb : |(Q.b r : ℝ)| ≤ Q.U := by exact_mod_cast Q.abs_b_le r
        have := Q.abs_colR_le j r
        gcongr
    _ = M * Q.U ^ 2 / Q.T := by simp; ring
    _ ≤ 1 / 8 := by rw [div_le_iff₀ hT]; linarith

/-- Generic part (c): `ν_j + 1 ≤ ν_{j'}` implies `‖p_j‖ < ‖p_{j'}‖`. -/
lemma normSq_lt_of_nu (hM : 2 ≤ M) {j j' : Fin (L + 1)} (h : Q.nu j + 1 ≤ Q.nu j') :
    normSq (Q.atom j) < normSq (Q.atom j') := by
  rw [normSq_atom, normSq_atom]
  have h1 := Q.abs_colR_beta_le hM j
  have h2 := Q.abs_colR_beta_le hM j'
  rw [abs_le] at h1 h2
  have hnu : (Q.nu j : ℝ) + 1 ≤ Q.nu j' := by exact_mod_cast h
  have hg' : (1 : ℝ) ≤ Q.gamma j' := by exact_mod_cast Q.one_le_gamma j'
  have hg : |(Q.gamma j : ℝ)| ≤ Q.K := by exact_mod_cast Q.abs_gamma_le j
  have hg2 : (Q.gamma j : ℝ) ^ 2 ≤ (Q.K : ℝ) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hg 2
  have hT : (1 : ℝ) ≤ Q.T := by exact_mod_cast Q.one_le_T
  have hNK : (4 * Q.T * Q.K ^ 2 : ℝ) ≤ (Q.N : ℝ) ^ 2 := by
    exact_mod_cast Q.four_T_K_sq_le_N_sq (by omega)
  have hK : (0 : ℝ) ≤ (Q.K : ℝ) ^ 2 := by positivity
  set a : ℝ := (Q.N : ℝ) ^ 2 with ha
  have ha0 : 0 < a := by have := Q.N_pos' (by omega : 1 ≤ M); positivity
  have h4 : (Q.N : ℝ) ^ 4 = a * a := by rw [ha]; ring
  rw [h4]
  set X := ∑ r, Q.colR j r * ((Q.b r : ℝ) / Q.T)
  set X' := ∑ r, Q.colR j' r * ((Q.b r : ℝ) / Q.T)
  set Y := ∑ r, ((Q.b r : ℝ) / Q.T) ^ 2
  have hdiff : (1 / 2 : ℝ) ≤ (Q.nu j' - 2 * X' + Y) - (Q.nu j - 2 * X + Y) := by linarith
  have hgg : 1 - (Q.K : ℝ) ^ 2 ≤ (Q.gamma j' : ℝ) ^ 2 - (Q.gamma j : ℝ) ^ 2 := by nlinarith
  have hK4 : 4 * (Q.K : ℝ) ^ 2 ≤ a := by nlinarith
  have e1 : a * (1 / 2) ≤ a * ((Q.nu j' - 2 * X' + Y) - (Q.nu j - 2 * X + Y)) :=
    mul_le_mul_of_nonneg_left hdiff ha0.le
  have e2 : a * (1 - (Q.K : ℝ) ^ 2) ≤ a * ((Q.gamma j' : ℝ) ^ 2 - (Q.gamma j : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_left hgg ha0.le
  have e3 : a * (4 * (Q.K : ℝ) ^ 2) ≤ a * a := mul_le_mul_of_nonneg_left hK4 ha0.le
  nlinarith

end Generic


/-! ### The LPs (LP⁺) and (LP̃⁺) -/

section Shield

variable {m n : ℕ} (P : IntLP m n) (e : Fin m → Fin n)

/-- The label of row `r` of (LP⁺): `e i` for the row `i`, `ω` for the shield row. -/
def Eω : Fin (m + 1) → Fin (n + 1) :=
  Fin.snoc (α := fun _ ↦ Fin (n + 1)) (fun i ↦ Fin.castSucc (e i)) (Fin.last n)

@[simp] lemma Eω_castSucc (i : Fin m) : Eω e (Fin.castSucc i) = Fin.castSucc (e i) := by
  simp [Eω]

@[simp] lemma Eω_last : Eω e (Fin.last m) = Fin.last n := by
  simp [Eω]

lemma initE_injective (hB₀ : P.toLP.IsBasis (basisOf e)) : Function.Injective e := by
  have h : (univ.image e).card = (univ : Finset (Fin m)).card := by
    rw [card_univ, Fintype.card_fin]; exact hB₀.1
  rw [Finset.card_image_iff, coe_univ] at h
  exact Set.injOn_univ.1 h

lemma Eω_injective (he : Function.Injective e) : Function.Injective (Eω e) := by
  intro a b h
  induction a using Fin.lastCases with
  | last =>
    induction b using Fin.lastCases with
    | last => rfl
    | cast b => simp at h; exact absurd h.symm (Fin.castSucc_ne_last _)
  | cast a =>
    induction b using Fin.lastCases with
    | last => simp at h
    | cast b =>
      have h' : e a = e b := by simpa using h
      rw [he h']

lemma hat_basisOf_eq : hat (basisOf e) = univ.image (Eω e) := by
  ext j
  simp only [hat, basisOf, mem_insert, mem_map, mem_image, mem_univ, true_and,
    Fin.castSuccEmb_apply]
  constructor
  · rintro (rfl | ⟨k, ⟨i, rfl⟩, rfl⟩)
    · exact ⟨Fin.last m, Eω_last e⟩
    · exact ⟨Fin.castSucc i, Eω_castSucc e i⟩
  · rintro ⟨r, rfl⟩
    induction r using Fin.lastCases with
    | last => left; simp
    | cast i => right; exact ⟨e i, ⟨i, rfl⟩, by simp⟩

lemma initMem_basisOf {k : Fin n} : k ∈ basisOf e ↔ ∃ i, e i = k := by
  simp [basisOf]

lemma not_mem_image_Eω {k : Fin (n + 1)} (hk : k ∉ univ.image (Eω e)) :
    ∃ k0, k = Fin.castSucc k0 ∧ k0 ∉ basisOf e := by
  induction k using Fin.lastCases with
  | last => exact absurd (mem_image.2 ⟨Fin.last m, mem_univ _, Eω_last e⟩) hk
  | cast k0 =>
    refine ⟨k0, rfl, fun h ↦ hk ?_⟩
    obtain ⟨i, rfl⟩ := (initMem_basisOf e).1 h
    exact mem_image.2 ⟨Fin.castSucc i, mem_univ _, Eω_castSucc e i⟩

lemma shield_A_Eω (hB₀ : P.toLP.IsBasis (basisOf e)) (r r' : Fin (m + 1)) :
    (P.shieldLP e).A r (Eω e r') = if r = r' then P.Delta0 e else 0 := by
  induction r using Fin.lastCases with
  | last =>
    induction r' using Fin.lastCases with
    | last => simp [shieldLP]
    | cast i' =>
      simp [shieldLP, (Fin.castSucc_ne_last i').symm, initMem_basisOf]
  | cast i =>
    induction r' using Fin.lastCases with
    | last => simp [shieldLP, Fin.castSucc_ne_last]
    | cast i' =>
      simp [shieldLP, canonical_A_apply_e P e hB₀]

lemma shield_c_Eω (hB₀ : P.toLP.IsBasis (basisOf e)) (r : Fin (m + 1)) :
    (P.shieldLP e).c (Eω e r) = 0 := by
  induction r using Fin.lastCases with
  | last => simp [shieldLP]
  | cast i => simp [shieldLP, canonical_c_apply_e P e hB₀]

lemma shield_b_pos (hP : P.IsAdmissible) (hB₀ : P.toLP.IsFeasibleBasis (basisOf e))
    (r : Fin (m + 1)) : 0 < (P.shieldLP e).b r := by
  induction r using Fin.lastCases with
  | last => simp [shieldLP]
  | cast i =>
    have := two_le_canonical_b P e hP hB₀ i
    simp only [shieldLP, Fin.snoc_castSucc]; omega

lemma one_le_Delta0 (hB₀ : P.toLP.IsBasis (basisOf e)) : 1 ≤ P.Delta0 e := by
  have := Delta0_pos P e hB₀; omega

lemma one_le_shieldW (hB₀ : P.toLP.IsBasis (basisOf e)) : 1 ≤ P.shieldW e := by
  have := one_le_Delta0 P e hB₀
  have := shieldCoeff_ge P e
  have := shieldW_ge P e
  omega

lemma one_le_shieldRank (σ : Equiv.Perm (Fin n)) (j : Fin (n + 1)) : 1 ≤ shieldRank σ j := by
  induction j using Fin.lastCases with
  | last => simp [shieldRank]
  | cast k => simp [shieldRank]

/-- The diagonal entries `d_ℓ = r(ℓ) W` of (LP̃⁺). -/
def dW (σ : Equiv.Perm (Fin n)) (r : Fin (m + 1)) : ℤ :=
  (shieldRank σ (Eω e r) : ℤ) * P.shieldW e

lemma one_le_dW (hB₀ : P.toLP.IsBasis (basisOf e)) (σ : Equiv.Perm (Fin n)) (r : Fin (m + 1)) :
    1 ≤ P.dW e σ r := by
  have h1 : (1 : ℤ) ≤ shieldRank σ (Eω e r) := by exact_mod_cast one_le_shieldRank σ _
  have h2 := one_le_shieldW P e hB₀
  unfold dW; nlinarith

lemma weighted_A_Eω (hB₀ : P.toLP.IsBasis (basisOf e)) (σ : Equiv.Perm (Fin n))
    (r r' : Fin (m + 1)) :
    (P.weightedLP e σ).A r (Eω e r') = if r = r' then P.dW e σ r' else 0 := by
  have he := initE_injective P e hB₀
  induction r using Fin.lastCases with
  | last =>
    induction r' using Fin.lastCases with
    | last => simp [weightedLP, dW]
    | cast i' =>
      simp [weightedLP, (Fin.castSucc_ne_last i').symm, initMem_basisOf]
  | cast i =>
    induction r' using Fin.lastCases with
    | last => simp [weightedLP, Fin.castSucc_ne_last]
    | cast i' =>
      simp only [weightedLP, Eω_castSucc, Matrix.of_apply, Fin.snoc_castSucc, dW]
      rw [ite_eq_left ((initMem_basisOf e).2 ⟨i', rfl⟩)]
      simp [he.eq_iff]

lemma weighted_c_Eω (hB₀ : P.toLP.IsBasis (basisOf e)) (σ : Equiv.Perm (Fin n))
    (r : Fin (m + 1)) : (P.weightedLP e σ).c (Eω e r) = 0 :=
  shield_c_Eω P e hB₀ r

/-- The estimate for the gap of a label `k ∉ B₀ ∪ {ω}`: the sum `∑_{ℓ ∈ R} A_{ℓk} b_ℓ`
is at most `-Δ₀ ≤ -1`. -/
lemma sum_R_le (hP : P.IsAdmissible) (hB₀ : P.toLP.IsFeasibleBasis (basisOf e))
    {k0 : Fin n} (hk0 : k0 ∉ basisOf e) (R : Finset (Fin (m + 1))) (hR : Fin.last m ∈ R)
    (f : Fin (m + 1) → ℤ) (hf : ∀ i, f (Fin.castSucc i) =
      (P.canonical e).A i k0 * (P.canonical e).b i) (hl : f (Fin.last m) ≤ -P.shieldCoeff e) :
    ∑ i ∈ R, f i ≤ -1 := by
  classical
  have hs := shield_sum_le P e hP hB₀ k0 hk0
  have hD := one_le_Delta0 P e hB₀.1
  have h1 : ∑ i ∈ R, f i = ∑ i, if i ∈ R then f i else 0 := by
    rw [Finset.sum_ite_mem, univ_inter]
  rw [h1, Fin.sum_univ_castSucc, ite_eq_left hR]
  have h2 : ∑ i : Fin m, (if Fin.castSucc i ∈ R then f (Fin.castSucc i) else 0) ≤
      ∑ i, (P.canonical e).b i * max ((P.canonical e).A i k0) 0 := by
    refine Finset.sum_le_sum fun i _ ↦ ?_
    have hb := two_le_canonical_b P e hP hB₀ i
    have hm1 : 0 ≤ max ((P.canonical e).A i k0) 0 := le_max_right _ _
    have hm2 : (P.canonical e).A i k0 ≤ max ((P.canonical e).A i k0) 0 := le_max_left _ _
    split_ifs
    · rw [hf]; nlinarith
    · positivity
  linarith


lemma shield_hneg (hP : P.IsAdmissible) (hB₀ : P.toLP.IsFeasibleBasis (basisOf e))
    {S : Finset (Fin (n + 2))} (hω : Fin.castSucc (Fin.last n) ∉ S) :
    ∀ k, k ∉ univ.image (Eω e) →
      ∑ i ∈ rowsOut (Eω e) S, (P.shieldLP e).A i k * (P.shieldLP e).b i ≤ -1 := by
  intro k hk
  obtain ⟨k0, rfl, hk0⟩ := not_mem_image_Eω e hk
  refine sum_R_le P e hP hB₀ hk0 _ (by simp [rowsOut, hω]) _ (fun i ↦ ?_) ?_
  · simp [shieldLP]
  · simp [shieldLP, hk0]

lemma weighted_hneg (hP : P.IsAdmissible) (hB₀ : P.toLP.IsFeasibleBasis (basisOf e))
    (σ : Equiv.Perm (Fin n))
    {S : Finset (Fin (n + 2))} (hω : Fin.castSucc (Fin.last n) ∉ S) :
    ∀ k, k ∉ univ.image (Eω e) →
      ∑ i ∈ rowsOut (Eω e) S, (P.weightedLP e σ).A i k * (P.weightedLP e σ).b i ≤ -1 := by
  intro k hk
  obtain ⟨k0, rfl, hk0⟩ := not_mem_image_Eω e hk
  refine sum_R_le P e hP hB₀ hk0 _ (by simp [rowsOut, hω]) _ (fun i ↦ ?_) ?_
  · simp [weightedLP, shieldLP, hk0]
  · have hD := one_le_Delta0 P e hB₀.1
    have ha := shieldCoeff_ge P e
    have hW := shieldW_ge P e
    have hr : (1 : ℤ) ≤ shieldRank σ (Fin.castSucc k0) := by
      exact_mod_cast one_le_shieldRank σ _
    simp only [weightedLP, shieldLP, Matrix.of_apply, Fin.snoc_last, Fin.snoc_castSucc, hk0,
      ite_false, mul_one]
    nlinarith

lemma one_le_sq_of_one_le_abs {z : ℤ} (h : 1 ≤ |z|) : 1 ≤ z ^ 2 := by
  rw [← sq_abs]; nlinarith

omit P e in
lemma sq_le_nu {M L : ℕ} (Q : IntLP M L) (r : Fin M) (k : Fin L) :
    Q.A r k ^ 2 ≤ Q.nu (Fin.castSucc k) := by
  simp only [nu, Fin.snoc_castSucc]
  exact Finset.single_le_sum (f := fun r ↦ Q.A r k ^ 2) (fun r _ ↦ sq_nonneg _) (mem_univ r)

omit P e in
@[simp] lemma nu_last {M L : ℕ} (Q : IntLP M L) : Q.nu (Fin.last L) = 0 := by
  simp [nu]

lemma nuW_castSucc_castSucc (hB₀ : P.toLP.IsBasis (basisOf e)) (σ : Equiv.Perm (Fin n))
    (k : Fin n) :
    (((σ k : ℕ) + 1 : ℤ) * P.shieldW e) ^ 2 ≤ (P.weightedLP e σ).nu k.castSucc.castSucc ∧
    (P.weightedLP e σ).nu k.castSucc.castSucc ≤
      (((σ k : ℕ) + 1 : ℤ) * P.shieldW e) ^ 2 + P.shieldW e - 1 := by
  have he := initE_injective P e hB₀
  have hW1 := one_le_shieldW P e hB₀
  simp only [nu, Fin.snoc_castSucc, Fin.sum_univ_castSucc]
  by_cases hk : k ∈ basisOf e
  · obtain ⟨i0, rfl⟩ := (initMem_basisOf e).1 hk
    simp only [weightedLP, Matrix.of_apply, Fin.snoc_castSucc, Fin.snoc_last, hk, ite_true,
      he.eq_iff, shieldRank]
    have : ∑ i : Fin m, (if i = i0 then ((σ (e i0) : ℕ) + 1 : ℤ) * P.shieldW e else 0) ^ 2 =
        (((σ (e i0) : ℕ) + 1 : ℤ) * P.shieldW e) ^ 2 := by
      simp [ite_pow]
    push_cast at this ⊢
    rw [this]
    constructor <;> nlinarith
  · simp only [weightedLP, Matrix.of_apply, Fin.snoc_castSucc, Fin.snoc_last, hk, ite_false,
      shieldRank]
    have h1 := shieldW_sum_le P e k hk
    have h2 : 0 ≤ ∑ i, (P.canonical e).A i k ^ 2 := Finset.sum_nonneg fun i _ ↦ sq_nonneg _
    have hD := one_le_Delta0 P e hB₀
    have ha := shieldCoeff_ge P e
    push_cast
    constructor <;> nlinarith

lemma nuW_omega (σ : Equiv.Perm (Fin n)) :
    (P.weightedLP e σ).nu (Fin.last n).castSucc = (((n : ℤ) + 1) * P.shieldW e) ^ 2 := by
  simp [nu, Fin.sum_univ_castSucc, weightedLP, shieldRank]

end Shield

/-! ### Lemma 13 (`lem:init`) and Lemma 16 (`lem:weighted`)(b),(c) -/

section Main

variable {m n : ℕ}

theorem init_a_main (P : IntLP m n) (hP : P.IsAdmissible) (e : Fin m → Fin n)
    (hB₀ : P.toLP.IsFeasibleBasis (basisOf e))
    (S : Finset (Fin (n + 2))) (hS : Fin.last (n + 1) ∈ S) (hSB : S ⊆ hat (hat (basisOf e))) :
    IsCorral (P.shieldLP e).atom S := by
  rw [hat_basisOf_eq] at hSB
  exact (diag_corral (P.shieldLP e) (Eω_injective e (initE_injective P e hB₀.1))
    (shield_c_Eω P e hB₀.1) (d := fun _ ↦ P.Delta0 e) (fun _ ↦ one_le_Delta0 P e hB₀.1)
    (shield_A_Eω P e hB₀.1) (shield_b_pos P e hP hB₀) (by omega) hS hSB).1


theorem init_b_main (P : IntLP m n) (hP : P.IsAdmissible) (e : Fin m → Fin n)
    (hB₀ : P.toLP.IsFeasibleBasis (basisOf e))
    (S : Finset (Fin (n + 2))) (hS : Fin.last (n + 1) ∈ S) (hSB : S ⊆ hat (hat (basisOf e)))
    (hω : Fin.castSucc (Fin.last n) ∉ S) :
    improving (P.shieldLP e).atom (affineMin (P.shieldLP e).atom S) =
      (hat (basisOf e)).map Fin.castSuccEmb \ S ∧
    (∀ ℓ : Fin (m + 1), Fin.castSucc (Fin.snoc (α := fun _ ↦ Fin (n + 1))
          (fun i ↦ Fin.castSucc (e i)) (Fin.last n) ℓ) ∉ S →
      gap (P.shieldLP e).atom (Fin.castSucc (Fin.snoc (α := fun _ ↦ Fin (n + 1))
          (fun i ↦ Fin.castSucc (e i)) (Fin.last n) ℓ)) (affineMin (P.shieldLP e).atom S) =
        -((P.shieldLP e).N : ℝ) ^ 4 * P.Delta0 e * ((P.shieldLP e).b ℓ / (P.shieldLP e).T)) ∧
    ∀ ℓ ∈ improving (P.shieldLP e).atom (affineMin (P.shieldLP e).atom S),
      ∀ S', MajorCycle (P.shieldLP e).atom S ℓ S' ↔ S' = insert ℓ S := by
  rw [hat_basisOf_eq] at hSB ⊢
  have hE := Eω_injective e (initE_injective P e hB₀.1)
  have hc := shield_c_Eω P e hB₀.1
  have hd : ∀ _r : Fin (m + 1), 1 ≤ P.Delta0 e := fun _ ↦ one_le_Delta0 P e hB₀.1
  have hA := shield_A_Eω P e hB₀.1
  have hb := shield_b_pos P e hP hB₀
  have hneg := shield_hneg P e hP hB₀ hω
  refine ⟨diag_improving (P.shieldLP e) hE hc (d := fun _ ↦ P.Delta0 e) hd hA hb (by omega)
      hS hSB hneg, fun ℓ hℓ ↦ ?_,
    diag_major (P.shieldLP e) hE hc (d := fun _ ↦ P.Delta0 e) hd hA hb (by omega) hS hSB hneg⟩
  change Fin.castSucc (Eω e ℓ) ∉ S at hℓ
  change gap _ (Fin.castSucc (Eω e ℓ)) _ = _
  rw [(diag_corral (P.shieldLP e) hE hc (d := fun _ ↦ P.Delta0 e) hd hA hb (by omega)
    hS hSB).2.1, gap_wR_E (P.shieldLP e) (d := fun _ ↦ P.Delta0 e) hc hA,
    ite_eq_left (by simp [rowsOut, hℓ])]

theorem init_c_main (P : IntLP m n) (hP : P.IsAdmissible) (e : Fin m → Fin n)
    (hB₀ : P.toLP.IsFeasibleBasis (basisOf e)) :
    ∀ j ≠ Fin.last (n + 1),
      normSq ((P.shieldLP e).atom (Fin.last (n + 1))) < normSq ((P.shieldLP e).atom j) := by
  intro j hj
  have hM : 2 ≤ m + 1 := by have := hP.1; omega
  apply normSq_lt_of_nu _ hM
  rw [nu_last, zero_add]
  induction j using Fin.lastCases with
  | last => exact absurd rfl hj
  | cast k =>
    have hD := one_le_Delta0 P e hB₀.1
    by_cases hk : k ∈ univ.image (Eω e)
    · obtain ⟨r, -, rfl⟩ := mem_image.1 hk
      refine le_trans ?_ (sq_le_nu _ r _)
      rw [shield_A_Eω P e hB₀.1, ite_eq_left rfl]
      nlinarith
    · obtain ⟨k0, rfl, hk0⟩ := not_mem_image_Eω e hk
      refine le_trans ?_ (sq_le_nu _ (Fin.last m) _)
      have ha := shieldCoeff_ge P e
      simp only [shieldLP, Matrix.of_apply, Fin.snoc_last, Fin.snoc_castSucc, hk0, ite_false]
      nlinarith

theorem weighted_b_main (P : IntLP m n) (hP : P.IsAdmissible) (e : Fin m → Fin n)
    (hB₀ : P.toLP.IsFeasibleBasis (basisOf e)) (σ : Equiv.Perm (Fin n))
    (S : Finset (Fin (n + 2))) (hS : Fin.last (n + 1) ∈ S) (hSB : S ⊆ hat (hat (basisOf e))) :
    IsCorral (P.weightedLP e σ).atom S ∧
    (Fin.castSucc (Fin.last n) ∉ S →
      improving (P.weightedLP e σ).atom (affineMin (P.weightedLP e σ).atom S) =
        (hat (basisOf e)).map Fin.castSuccEmb \ S ∧
      ∀ ℓ ∈ improving (P.weightedLP e σ).atom (affineMin (P.weightedLP e σ).atom S),
        ∀ S', MajorCycle (P.weightedLP e σ).atom S ℓ S' ↔ S' = insert ℓ S) := by
  rw [hat_basisOf_eq] at hSB ⊢
  have hE := Eω_injective e (initE_injective P e hB₀.1)
  have hc := weighted_c_Eω P e hB₀.1 σ
  have hd := one_le_dW P e hB₀.1 σ
  have hA := weighted_A_Eω P e hB₀.1 σ
  have hb : ∀ r, 0 < (P.weightedLP e σ).b r := shield_b_pos P e hP hB₀
  refine ⟨(diag_corral (P.weightedLP e σ) hE hc hd hA hb (by omega) hS hSB).1,
    fun hω ↦ ⟨?_, ?_⟩⟩
  · exact diag_improving (P.weightedLP e σ) hE hc hd hA hb (by omega) hS hSB
      (weighted_hneg P e hP hB₀ σ hω)
  · exact diag_major (P.weightedLP e σ) hE hc hd hA hb (by omega) hS hSB
      (weighted_hneg P e hP hB₀ σ hω)

theorem weighted_c_main (P : IntLP m n) (hP : P.IsAdmissible) (e : Fin m → Fin n)
    (hB₀ : P.toLP.IsFeasibleBasis (basisOf e)) (σ : Equiv.Perm (Fin n)) :
    let p := (P.weightedLP e σ).atom
    (∀ k : Fin n, normSq (p (Fin.last (n + 1))) < normSq (p k.castSucc.castSucc)) ∧
    (∀ k k' : Fin n, σ k < σ k' →
      normSq (p k.castSucc.castSucc) < normSq (p k'.castSucc.castSucc)) ∧
    (∀ k : Fin n, normSq (p k.castSucc.castSucc) < normSq (p (Fin.last n).castSucc)) := by
  intro p
  have hM : 2 ≤ m + 1 := by have := hP.1; omega
  have hW := one_le_shieldW P e hB₀.1
  refine ⟨fun k ↦ ?_, fun k k' hkk' ↦ ?_, fun k ↦ ?_⟩
  · apply normSq_lt_of_nu _ hM
    rw [nu_last, zero_add]
    have h := (nuW_castSucc_castSucc P e hB₀.1 σ k).1
    have h1 : (1 : ℤ) ≤ ((σ k : ℕ) + 1 : ℤ) := by omega
    have h2 : (1 : ℤ) ≤ ((σ k : ℕ) + 1 : ℤ) * P.shieldW e := one_le_mul_of_one_le_of_one_le h1 hW
    have h3 : (1 : ℤ) ≤ (((σ k : ℕ) + 1 : ℤ) * P.shieldW e) ^ 2 := one_le_pow₀ h2
    linarith
  · apply normSq_lt_of_nu _ hM
    have h1 := (nuW_castSucc_castSucc P e hB₀.1 σ k).2
    have h2 := (nuW_castSucc_castSucc P e hB₀.1 σ k').1
    have h3 : ((σ k : ℕ) + 1 : ℤ) + 1 ≤ ((σ k' : ℕ) + 1 : ℤ) := by
      have : (σ k : ℕ) < σ k' := hkk'
      omega
    have h4 : (0 : ℤ) ≤ ((σ k : ℕ) + 1 : ℤ) := by omega
    have h5 : (((σ k : ℕ) + 1 : ℤ) + 1) * P.shieldW e ≤ ((σ k' : ℕ) + 1 : ℤ) * P.shieldW e :=
      mul_le_mul_of_nonneg_right h3 (by omega)
    have h6 : ((((σ k : ℕ) + 1 : ℤ) + 1) * P.shieldW e) ^ 2 ≤
        (((σ k' : ℕ) + 1 : ℤ) * P.shieldW e) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h5 2
    have h7 : (((σ k : ℕ) + 1 : ℤ) * P.shieldW e) ^ 2 + P.shieldW e ≤
        ((((σ k : ℕ) + 1 : ℤ) + 1) * P.shieldW e) ^ 2 := by
      have := mul_nonneg h4 (by positivity : (0 : ℤ) ≤ P.shieldW e * P.shieldW e)
      nlinarith
    linarith
  · apply normSq_lt_of_nu _ hM
    rw [nuW_omega]
    have h1 := (nuW_castSucc_castSucc P e hB₀.1 σ k).2
    have h3 : ((σ k : ℕ) + 1 : ℤ) + 1 ≤ (n : ℤ) + 1 := by
      have : (σ k : ℕ) < n := (σ k).isLt
      omega
    have h4 : (0 : ℤ) ≤ ((σ k : ℕ) + 1 : ℤ) := by omega
    have h5 : (((σ k : ℕ) + 1 : ℤ) + 1) * P.shieldW e ≤ ((n : ℤ) + 1) * P.shieldW e :=
      mul_le_mul_of_nonneg_right h3 (by omega)
    have h6 : ((((σ k : ℕ) + 1 : ℤ) + 1) * P.shieldW e) ^ 2 ≤
        (((n : ℤ) + 1) * P.shieldW e) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h5 2
    have h7 : (((σ k : ℕ) + 1 : ℤ) * P.shieldW e) ^ 2 + P.shieldW e ≤
        ((((σ k : ℕ) + 1 : ℤ) + 1) * P.shieldW e) ^ 2 := by
      have := mul_nonneg h4 (by positivity : (0 : ℤ) ≤ P.shieldW e * P.shieldW e)
      nlinarith
    linarith

end Main

end WolfeSimplex.IntLP
