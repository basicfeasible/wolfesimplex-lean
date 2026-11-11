import WolfeSimplex.Defs.InducedBasis
import WolfeSimplex.Proofs.AffineMin
import WolfeSimplex.Proofs.Pivot
import WolfeSimplex.Proofs.RuleRuns
import WolfeSimplex.Proofs.Identities
import WolfeSimplex.Proofs.InducedLemmasTBound

/-!
# The lemmas of Section 3 (`sec:equivalence`) about the induced LP (LP_λ)

Proofs of Lemma 9 (`lem:induced-facts`), Lemma 3 (`lem:direction`), Lemma 4 (`lem:corral`) (for an
arbitrary basis
`S` of the induced LP), Lemma 2 (`lem:hom`), Lemma 5 (`lem:bases-corrals`), Lemma 6 (`lem:pivot`),
Lemma 10 (`lem:encoding`).
-/

namespace WolfeSimplex

namespace IntLP

open Finset Matrix Wolfe

variable {m n : ℕ} (P : IntLP m n)

/-! ### The induced LP in terms of `acomb` -/

@[simp] lemma inducedLP_c (k : Fin (n + 1)) : P.inducedLP.c k = (P.gamma k : ℝ) := rfl

lemma inducedLP_b : P.inducedLP.b = Fin.snoc (α := fun _ ↦ ℝ) 0 1 := rfl

lemma inducedLP_col (k : Fin (n + 1)) :
    P.inducedLP.col k = Fin.snoc (α := fun _ ↦ ℝ) (P.alpha k) 1 := by
  funext r; simp [LP.col, inducedLP]

/-- `M β = (∑ β_k α_k, ∑ β_k)ᵀ`. -/
lemma inducedLP_mulVec (β : Fin (n + 1) → ℝ) :
    P.inducedLP.A *ᵥ β = Fin.snoc (α := fun _ ↦ ℝ) (P.acomb β) (∑ k, β k) := by
  funext r
  induction r using Fin.lastCases with
  | last => simp [inducedLP, mulVec, dotProduct]
  | cast i => simp [inducedLP, mulVec, dotProduct, acomb, mul_comm]

lemma acomb_eq_of_mulVec {β : Fin (n + 1) → ℝ} {a : Fin m → ℝ} {s : ℝ}
    (h : P.inducedLP.A *ᵥ β = Fin.snoc (α := fun _ ↦ ℝ) a s) : P.acomb β = a ∧ ∑ k, β k = s := by
  rw [inducedLP_mulVec] at h
  refine ⟨funext fun i ↦ ?_, ?_⟩
  · have := congrFun h (Fin.castSucc i); simpa using this
  · have := congrFun h (Fin.last m); simpa using this

/-- `(v, h) M_k = v ᵀ α_k + h`. -/
lemma dualVec_dot_col (S : Finset (Fin (n + 1))) (k : Fin (n + 1)) :
    P.inducedLP.dualVec S ⬝ᵥ P.inducedLP.col k = ∑ i, P.vS S i * P.alpha k i + P.hS S := by
  rw [inducedLP_col, dotProduct, Fin.sum_univ_castSucc]
  simp [vS, hS]

lemma reducedCost_eq (S : Finset (Fin (n + 1))) (k : Fin (n + 1)) :
    P.inducedLP.reducedCost S k = (P.gamma k : ℝ) - ∑ i, P.vS S i * P.alpha k i - P.hS S := by
  rw [LP.reducedCost, dualVec_dot_col, inducedLP_c]; ring

variable {P}

/-- Equation 19 (`eq:dual`): `vᵀ α_i + h = γ_i` for `i ∈ S`. -/
lemma dual_eq {S : Finset (Fin (n + 1))} (hS : P.inducedLP.IsBasis S) {k : Fin (n + 1)}
    (hk : k ∈ S) : ∑ i, P.vS S i * P.alpha k i + P.hS S = (P.gamma k : ℝ) := by
  have := hS.reducedCost_of_mem hk
  rw [reducedCost_eq] at this; linarith

/-- `γᵀ x = vᵀ (∑ x_k α_k) + h ∑ x_k` for `x` vanishing off a basis `S`. -/
lemma gamma_dot_of_vanish {S : Finset (Fin (n + 1))} (hS : P.inducedLP.IsBasis S)
    {x : Fin (n + 1) → ℝ} (hx : ∀ k ∉ S, x k = 0) :
    ∑ k, (P.gamma k : ℝ) * x k = ∑ i, P.vS S i * P.acomb x i + P.hS S * ∑ k, x k := by
  have h := hS.cost_eq x
  have h0 : ∑ k, P.inducedLP.reducedCost S k * x k = 0 := by
    refine Finset.sum_eq_zero fun k _ ↦ ?_
    by_cases hk : k ∈ S
    · simp [hS.reducedCost_of_mem hk]
    · simp [hx k hk]
  rw [h0, add_zero, inducedLP_mulVec] at h
  have e : P.inducedLP.dualVec S ⬝ᵥ Fin.snoc (α := fun _ ↦ ℝ) (P.acomb x) (∑ k, x k) =
      ∑ i, P.vS S i * P.acomb x i + P.hS S * ∑ k, x k := by
    rw [dotProduct, Fin.sum_univ_castSucc]; simp [vS, IntLP.hS]
  rw [← e, ← h, dotProduct]
  rfl

/-! ### Lemma 9 (`lem:induced-facts`) -/

lemma basicSol_acomb {S : Finset (Fin (n + 1))} (hS : P.inducedLP.IsBasis S) :
    P.acomb (P.inducedLP.basicSol S) = 0 ∧ ∑ k, P.inducedLP.basicSol S k = 1 :=
  P.acomb_eq_of_mulVec hS.basicSol_spec.1

lemma basicDir_acomb {S : Finset (Fin (n + 1))} (hS : P.inducedLP.IsBasis S)
    {j : Fin (n + 1)} (hj : j ∉ S) :
    P.acomb (P.inducedLP.basicDir S j) = 0 ∧ ∑ k, P.inducedLP.basicDir S j k = 0 := by
  have h := (hS.basicDir_spec hj).1
  have : (0 : Fin (m + 1) → ℝ) = Fin.snoc (α := fun _ ↦ ℝ) 0 0 := by
    funext r; induction r using Fin.lastCases <;> simp
  rw [this] at h
  exact P.acomb_eq_of_mulVec h

lemma sum_smul_alpha_eq (x : Fin (n + 1) → ℝ) :
    ∑ k, x k • P.alpha k = P.acomb x := by
  funext i; simp [acomb, Finset.sum_apply]

lemma gamma_basicSol {S : Finset (Fin (n + 1))} (hS : P.inducedLP.IsBasis S) :
    ∑ i, (P.gamma i : ℝ) * P.inducedLP.basicSol S i = P.hS S := by
  rw [gamma_dot_of_vanish hS hS.basicSol_spec.2, (basicSol_acomb hS).1, (basicSol_acomb hS).2]
  simp

lemma one_le_hS {S : Finset (Fin (n + 1))} (hS : P.inducedLP.IsFeasibleBasis S) :
    1 ≤ P.hS S := by
  rw [← gamma_basicSol hS.1, ← (basicSol_acomb hS.1).2]
  refine Finset.sum_le_sum fun k _ ↦ ?_
  have hg : (1 : ℝ) ≤ P.gamma k := by exact_mod_cast P.one_le_gamma k
  nlinarith [hS.2 k]

theorem induced_facts' (P : IntLP m n) (S : Finset (Fin (n + 1)))
    (hS : P.inducedLP.IsBasis S) (j : Fin (n + 1)) :
    (∑ i ∈ S, P.inducedLP.basicSol S i • P.alpha i = 0 ∧
      ∑ i ∈ S, P.inducedLP.basicSol S i = 1) ∧
    (∑ i, (P.gamma i : ℝ) * P.inducedLP.basicSol S i = P.hS S ∧
      (P.inducedLP.IsFeasibleBasis S → 1 ≤ P.hS S)) ∧
    (j ∉ S → ∑ k, P.inducedLP.basicDir S j k • P.alpha k = 0 ∧
      ∑ k, P.inducedLP.basicDir S j k = 0 ∧
      ∑ k, (P.gamma k : ℝ) * P.inducedLP.basicDir S j k = P.inducedLP.reducedCost S j) := by
  have hv := hS.basicSol_spec.2
  refine ⟨⟨?_, ?_⟩, ⟨gamma_basicSol hS, one_le_hS⟩, fun hj ↦ ⟨?_, (basicDir_acomb hS hj).2, ?_⟩⟩
  · rw [sum_eq_sum_univ_of S _ (fun k hk ↦ by simp [hv k hk]), sum_smul_alpha_eq,
      (basicSol_acomb hS).1]
  · rw [sum_eq_sum_univ_of S _ hv, (basicSol_acomb hS).2]
  · rw [sum_smul_alpha_eq, (basicDir_acomb hS hj).1]
  · rw [← hS.cost_basicDir hj, dotProduct]
    rfl

/-! ### Lemma 3 (`lem:direction`) -/

/-- `∑_k d_k f_k = f_j + ∑_{i∈S} d_i f_i` for the basic direction `d = d^{S,j}`. -/
lemma sum_basicDir {M : Type*} [AddCommMonoid M] [Module ℝ M] {S : Finset (Fin (n + 1))}
    (hS : P.inducedLP.IsBasis S) {j : Fin (n + 1)} (hj : j ∉ S) (f : Fin (n + 1) → M) :
    ∑ k, P.inducedLP.basicDir S j k • f k = f j + ∑ i ∈ S, P.inducedLP.basicDir S j i • f i := by
  obtain ⟨-, h1, h2⟩ := hS.basicDir_spec hj
  have hsub : ∑ k ∈ insert j S, P.inducedLP.basicDir S j k • f k =
      ∑ k, P.inducedLP.basicDir S j k • f k := by
    refine Finset.sum_subset (subset_univ _) fun k _ hk ↦ ?_
    have hkS : k ∉ S := fun h ↦ hk (mem_insert_of_mem h)
    have hkj : k ≠ j := fun h ↦ hk (h ▸ mem_insert_self _ _)
    simp [h2 k hkS hkj]
  rw [← hsub, sum_insert hj, h1, one_smul]

lemma gcomb_basicDir {S : Finset (Fin (n + 1))} (hS : P.inducedLP.IsBasis S)
    {j : Fin (n + 1)} (hj : j ∉ S) :
    P.gcomb (P.inducedLP.basicDir S j) = P.inducedLP.reducedCost S j := by
  rw [← hS.cost_basicDir hj, gcomb, dotProduct]
  exact Finset.sum_congr rfl fun k _ ↦ by simp [mul_comm]

lemma comb_basicDir {S : Finset (Fin (n + 1))} (hS : P.inducedLP.IsBasis S)
    {j : Fin (n + 1)} (hj : j ∉ S) :
    ∑ k, P.inducedLP.basicDir S j k • P.atom k =
      ((P.N : ℝ) * P.inducedLP.reducedCost S j) • Pi.single 0 1 := by
  rw [atom_comb, (basicDir_acomb hS hj).1, gcomb_basicDir hS hj]
  funext r
  induction r using Fin.cases with
  | zero => simp
  | succ i => simp [Fin.succ_ne_zero]

theorem direction' (P : IntLP m n) (S : Finset (Fin (n + 1))) (hS : P.inducedLP.IsBasis S)
    (j : Fin (n + 1)) (hj : j ∉ S) (w : Fin (m + 1) → ℝ) :
    P.atom j + ∑ i ∈ S, P.inducedLP.basicDir S j i • P.atom i =
      ((P.N : ℝ) * P.inducedLP.reducedCost S j) • Pi.single 0 1 ∧
    gap P.atom j w + ∑ i ∈ S, P.inducedLP.basicDir S j i * gap P.atom i w =
      (P.N : ℝ) * P.inducedLP.reducedCost S j * w 0 := by
  refine ⟨by rw [← sum_basicDir hS hj, comb_basicDir hS hj], ?_⟩
  have h := sum_basicDir hS hj (fun k ↦ gap P.atom k w)
  simp only [smul_eq_mul] at h
  rw [← h]
  have e : ∑ k, P.inducedLP.basicDir S j k * gap P.atom k w =
      (∑ k, P.inducedLP.basicDir S j k • P.atom k) ⬝ᵥ w -
        (∑ k, P.inducedLP.basicDir S j k) * normSq w := by
    simp only [gap, sum_dotProduct, smul_dotProduct, smul_eq_mul, mul_sub,
      Finset.sum_sub_distrib, Finset.sum_mul]
  rw [e, comb_basicDir hS hj, (basicDir_acomb hS hj).2]
  simp [smul_dotProduct]

/-! ### Lemma 4 (`lem:corral`) for an arbitrary basis `S` -/

lemma uS_spec {S : Finset (Fin (n + 1))} (hS : P.inducedLP.IsBasis S) : P.IsUSOf S (P.uS S) :=
  Classical.epsilon_spec (p := P.IsUSOf S) (hS.exists_sol _)

lemma uS_acomb {S : Finset (Fin (n + 1))} (hS : P.inducedLP.IsBasis S) :
    P.acomb (P.uS S) = P.vS S ∧ ∑ k, P.uS S k = 0 :=
  P.acomb_eq_of_mulVec (uS_spec hS).1

variable (P) in
lemma denomS_pos (hm : 1 ≤ m) (S : Finset (Fin (n + 1))) :
    0 < (P.N : ℝ) ^ 2 + P.vS S ⬝ᵥ P.vS S := by
  have := P.N_pos' hm
  have : 0 ≤ P.vS S ⬝ᵥ P.vS S := Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _
  positivity

variable (P) in
lemma epsS_mul (hm : 1 ≤ m) (S : Finset (Fin (n + 1))) :
    P.epsS S * ((P.N : ℝ) ^ 2 + P.vS S ⬝ᵥ P.vS S) = P.hS S := by
  rw [epsS, div_mul_cancel₀ _ (P.denomS_pos hm S).ne']

variable (P) in
lemma sS_eq (hm : 1 ≤ m) (S : Finset (Fin (n + 1))) :
    P.sS S = P.hS S - P.epsS S * (P.vS S ⬝ᵥ P.vS S) := by
  have := P.epsS_mul hm S
  rw [sS]; linarith

variable (P) in
/-- `λ^{*S} = λ^S - ε^S u^S`. -/
noncomputable def lamStarS (S : Finset (Fin (n + 1))) : Fin (n + 1) → ℝ :=
  P.inducedLP.basicSol S - P.epsS S • P.uS S

variable (P) in
/-- `w_S = (N s^S, -N² ε^S v^S)`. -/
noncomputable def wS (S : Finset (Fin (n + 1))) : Fin (m + 1) → ℝ :=
  Fin.cons (α := fun _ ↦ ℝ) ((P.N : ℝ) * P.sS S) (fun i ↦ -(P.N : ℝ) ^ 2 * P.epsS S * P.vS S i)

lemma lamStarS_eq_zero {S : Finset (Fin (n + 1))} (hS : P.inducedLP.IsBasis S) :
    ∀ k ∉ S, P.lamStarS S k = 0 := by
  intro k hk; simp [lamStarS, hS.basicSol_spec.2 k hk, (uS_spec hS).2 k hk]

lemma sum_lamStarS {S : Finset (Fin (n + 1))} (hS : P.inducedLP.IsBasis S) :
    ∑ k, P.lamStarS S k = 1 := by
  simp [lamStarS, Finset.sum_sub_distrib, ← Finset.mul_sum, (basicSol_acomb hS).2,
    (uS_acomb hS).2]

lemma acomb_lamStarS {S : Finset (Fin (n + 1))} (hS : P.inducedLP.IsBasis S) :
    P.acomb (P.lamStarS S) = -(P.epsS S) • P.vS S := by
  rw [lamStarS, acomb_sub, acomb_smul, (basicSol_acomb hS).1, (uS_acomb hS).1]
  simp

lemma gamma_lamStarS (hm : 1 ≤ m) {S : Finset (Fin (n + 1))} (hS : P.inducedLP.IsBasis S) :
    ∑ k, (P.gamma k : ℝ) * P.lamStarS S k = P.sS S := by
  rw [gamma_dot_of_vanish hS (lamStarS_eq_zero hS), acomb_lamStarS hS, sum_lamStarS hS,
    P.sS_eq hm S, dotProduct]
  simp only [Pi.smul_apply, smul_eq_mul, mul_one]
  have : ∑ i, P.vS S i * (-P.epsS S * P.vS S i) = -(P.epsS S * ∑ i, P.vS S i * P.vS S i) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [this]; ring

lemma comb_lamStarS (hm : 1 ≤ m) {S : Finset (Fin (n + 1))} (hS : P.inducedLP.IsBasis S) :
    ∑ k, P.lamStarS S k • P.atom k = P.wS S := by
  have hg : P.gcomb (P.lamStarS S) = P.sS S := by
    rw [← gamma_lamStarS hm hS, gcomb]
    exact Finset.sum_congr rfl fun k _ ↦ mul_comm _ _
  rw [atom_comb, hg, acomb_lamStarS hS, wS]
  congr 1
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

variable (P) in
/-- `g_j(w_S) = N² s^S γ̄^S_j` (Lemma 4 (`lem:corral`)(b)). -/
lemma gap_wS (hm : 1 ≤ m) (S : Finset (Fin (n + 1))) (k : Fin (n + 1)) :
    gap P.atom k (P.wS S) = (P.N : ℝ) ^ 2 * P.sS S * P.inducedLP.reducedCost S k := by
  rw [reducedCost_eq]
  have hden := P.epsS_mul hm S
  simp only [gap, normSq, dotProduct, Fin.sum_univ_succ, atom, wS, Fin.cons_zero,
    Fin.cons_succ, sS]
  have e1 : ∑ i, (P.N : ℝ) ^ 2 * P.alpha k i * (-(P.N : ℝ) ^ 2 * P.epsS S * P.vS S i) =
      -((P.N : ℝ) ^ 4 * P.epsS S) * ∑ i, P.vS S i * P.alpha k i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ ↦ by ring
  have e2 : ∑ i, (-(P.N : ℝ) ^ 2 * P.epsS S * P.vS S i) *
      (-(P.N : ℝ) ^ 2 * P.epsS S * P.vS S i) =
      ((P.N : ℝ) ^ 2 * P.epsS S) ^ 2 * (P.vS S ⬝ᵥ P.vS S) := by
    rw [dotProduct, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [e1, e2, ← hden]
  ring

lemma affIndep_of_basis (hm : 1 ≤ m) {S : Finset (Fin (n + 1))}
    (hS : P.inducedLP.IsBasis S) : IsAffinelyIndependent P.atom S := by
  classical
  intro β hcomb hsum i hi
  set β' : Fin (n + 1) → ℝ := fun k ↦ if k ∈ S then β k else 0 with hβ'
  have h0 : ∀ k ∉ S, β' k = 0 := fun k hk ↦ by simp [β', hk]
  have hc : ∑ k, β' k • P.atom k = 0 := by
    rw [← sum_eq_sum_univ_of S _ (fun k hk ↦ by simp [h0 k hk]), ← hcomb]
    exact Finset.sum_congr rfl fun k hk ↦ by simp [β', hk]
  have hs : ∑ k, β' k = 0 := by
    rw [← sum_eq_sum_univ_of S _ h0, ← hsum]
    exact Finset.sum_congr rfl fun k hk ↦ by simp [β', hk]
  have hac : P.acomb β' = 0 := by
    rw [atom_comb] at hc
    funext r
    have := congrFun hc r.succ
    simp only [Fin.cons_succ, Pi.zero_apply] at this
    have hN := (P.N_pos' hm).ne'
    simpa [hN] using this
  have hA : P.inducedLP.A *ᵥ β' = 0 := by
    rw [inducedLP_mulVec, hac, hs]
    funext r; induction r using Fin.lastCases <;> simp
  have := congrFun (hS.eq_zero h0 hA) i
  simpa [β', hi] using this

lemma affineMin_eq_wS (hm : 1 ≤ m) {S : Finset (Fin (n + 1))} (hS : P.inducedLP.IsBasis S) :
    affineMin P.atom S = P.wS S := by
  apply affineMin_eq_of_gap_zero
  · refine ⟨P.lamStarS S, ?_, ?_⟩
    · rw [sum_eq_sum_univ_of _ _ (lamStarS_eq_zero hS), sum_lamStarS hS]
    · rw [sum_eq_sum_univ_of _ _ (fun k hk ↦ by simp [lamStarS_eq_zero hS k hk]),
        comb_lamStarS hm hS]
  · intro i hi
    rw [P.gap_wS hm, hS.reducedCost_of_mem hi, mul_zero]

lemma affineCoeffs_eq_lamStarS (hm : 1 ≤ m) {S : Finset (Fin (n + 1))}
    (hS : P.inducedLP.IsBasis S) : affineCoeffs P.atom S = P.lamStarS S := by
  apply affineCoeffs_eq_of _ (affIndep_of_basis hm hS) (lamStarS_eq_zero hS)
  · rw [sum_eq_sum_univ_of _ _ (lamStarS_eq_zero hS), sum_lamStarS hS]
  · rw [affineMin_eq_wS hm hS,
      sum_eq_sum_univ_of _ _ (fun k hk ↦ by simp [lamStarS_eq_zero hS k hk]), comb_lamStarS hm hS]

lemma epsS_pos (hm : 1 ≤ m) {S : Finset (Fin (n + 1))} (hS : P.inducedLP.IsFeasibleBasis S) :
    0 < P.epsS S := by
  rw [epsS]
  exact div_pos (by linarith [one_le_hS hS]) (P.denomS_pos hm S)

theorem corral' (P : IntLP m n) (hP : P.IsAdmissible) (S : Finset (Fin (n + 1)))
    (hS : P.inducedLP.IsBasis S) :
    (IsAffinelyIndependent P.atom S ∧
      affineCoeffs P.atom S = P.inducedLP.basicSol S - P.epsS S • P.uS S ∧
      affineMin P.atom S = Fin.cons (α := fun _ ↦ ℝ) ((P.N : ℝ) * P.sS S)
        (fun i ↦ -(P.N : ℝ) ^ 2 * P.epsS S * P.vS S i) ∧
      ∑ i, (P.gamma i : ℝ) * affineCoeffs P.atom S i = P.sS S ∧
      P.sS S = P.hS S - P.epsS S * (P.vS S ⬝ᵥ P.vS S)) ∧
    (∀ j, gap P.atom j (affineMin P.atom S) =
      (P.N : ℝ) ^ 2 * P.sS S * P.inducedLP.reducedCost S j) ∧
    (P.inducedLP.IsFeasibleBasis S → 0 < P.sS S) := by
  have hm := hP.1
  refine ⟨⟨affIndep_of_basis hm hS, affineCoeffs_eq_lamStarS hm hS, affineMin_eq_wS hm hS, ?_,
    P.sS_eq hm S⟩, fun j ↦ ?_, fun hF ↦ ?_⟩
  · rw [affineCoeffs_eq_lamStarS hm hS, gamma_lamStarS hm hS]
  · -- Lemma 3 and Lemma 1(a): basic gaps vanish at the affine minimizer.
    have hne : S.Nonempty := Finset.card_pos.mp (by have := hS.1; omega)
    have hzero := (Wolfe.affineMin_spec hne (affIndep_of_basis hm hS)).2
    by_cases hj : j ∈ S
    · rw [hzero j hj, hS.reducedCost_of_mem hj, mul_zero]
    · have hd := (direction' P S hS j hj (affineMin P.atom S)).2
      have hsum : ∑ i ∈ S, P.inducedLP.basicDir S j i *
          gap P.atom i (affineMin P.atom S) = 0 :=
        Finset.sum_eq_zero fun i hi ↦ by rw [hzero i hi, mul_zero]
      rw [hsum, add_zero] at hd
      calc
        gap P.atom j (affineMin P.atom S) =
            (P.N : ℝ) * P.inducedLP.reducedCost S j * (affineMin P.atom S) 0 := hd
        _ = (P.N : ℝ) ^ 2 * P.sS S * P.inducedLP.reducedCost S j := by
          rw [affineMin_eq_wS hm hS, wS, Fin.cons_zero]
          ring
  · rw [sS]
    have := P.N_pos' hm
    have := epsS_pos hm hF
    positivity

/-! ### General LP facts -/

omit P in
lemma rank_eq_of_isBasis {m' n' : ℕ} {Q : LP m' n'} {S : Finset (Fin n')} (hS : Q.IsBasis S) :
    Q.A.rank = m' := by
  unfold Matrix.rank
  have : LinearMap.range Q.A.mulVecLin = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro r
    obtain ⟨x, hx, -⟩ := hS.exists_sol r
    exact ⟨x, by simpa using hx⟩
  rw [this, finrank_top, Module.finrank_fin_fun]

omit P in
lemma eq_dualVec {m' n' : ℕ} {Q : LP m' n'} {S : Finset (Fin n')} (hS : Q.IsBasis S)
    {y : Fin m' → ℝ} (hy : Q.IsDualVectorOf S y) : y = Q.dualVec S := by
  have hd := hS.dualVec_spec
  set z := y - Q.dualVec S with hz_def
  have hz : ∀ j ∈ S, z ⬝ᵥ Q.col j = 0 := fun j hj ↦ by
    rw [hz_def, sub_dotProduct, hy j hj, hd j hj, sub_self]
  obtain ⟨x, hx, hx0⟩ := hS.exists_sol z
  have h0 : z ⬝ᵥ z = 0 := by
    calc z ⬝ᵥ z = z ⬝ᵥ (Q.A *ᵥ x) := by rw [hx]
      _ = (z ᵥ* Q.A) ⬝ᵥ x := dotProduct_mulVec _ _ _
      _ = 0 := by
        rw [dotProduct]
        refine Finset.sum_eq_zero fun j _ ↦ ?_
        by_cases hj : j ∈ S
        · have : (z ᵥ* Q.A) j = 0 := hz j hj
          rw [this, zero_mul]
        · rw [hx0 j hj, mul_zero]
  exact sub_eq_zero.1 (dotProduct_self_eq_zero.1 h0)

omit P in
lemma snoc_zero_zero : Fin.snoc (α := fun _ ↦ ℝ) (0 : Fin m → ℝ) (0 : ℝ) = 0 := by
  funext r; induction r using Fin.lastCases <;> simp

/-! ### The basis `B̂` of the induced LP -/

variable {B : Finset (Fin n)}

lemma isBasis_hat (hB : P.toLP.IsBasis B) : P.inducedLP.IsBasis (hat B) := by
  refine ⟨by rw [card_hat, hB.1], (LP.linIndep_iff _ _).2 fun β hβ hA ↦ ?_⟩
  obtain ⟨hac, hs⟩ := P.acomb_eq_of_mulVec (a := 0) (s := 0) (by rw [hA, snoc_zero_zero])
  exact eq_zero_of_acomb hB hβ hac hs

lemma basicSol_hat (hB : P.toLP.IsBasis B) : P.inducedLP.basicSol (hat B) = P.lamHat B :=
  ((isBasis_hat hB).eq_basicSol (by rw [inducedLP_mulVec, acomb_lamHat hB, sum_lamHat]; rfl)
    (lamHat_eq_zero hB)).symm

lemma dualVec_hat (hB : P.toLP.IsBasis B) :
    P.inducedLP.dualVec (hat B) = Fin.snoc (α := fun _ ↦ ℝ) (P.yB B) (P.hHat B) := by
  refine (eq_dualVec (isBasis_hat hB) fun k hk ↦ ?_).symm
  have h := gamma_sub_eq_rcHat (P := P) (B := B) k
  rw [rcHat_eq_zero_of_mem hB hk] at h
  have e : ∑ i, P.yB B i * P.alpha k i = ∑ i, P.alpha k i * P.yB B i :=
    Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _
  rw [inducedLP_col, dotProduct, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, mul_one, inducedLP_c]
  linarith

lemma vS_hat (hB : P.toLP.IsBasis B) : P.vS (hat B) = P.toLP.dualVec B := by
  funext i; simp [vS, dualVec_hat hB, yB]

lemma hS_hat (hB : P.toLP.IsBasis B) : P.hS (hat B) = P.hHat B := by
  simp [IntLP.hS, dualVec_hat hB]

lemma reducedCost_hat (hB : P.toLP.IsBasis B) (k : Fin (n + 1)) :
    P.inducedLP.reducedCost (hat B) k = P.rcHat B k := by
  rw [reducedCost_eq, vS_hat hB, hS_hat hB, ← gamma_sub_eq_rcHat]
  have e : ∑ i, P.toLP.dualVec B i * P.alpha k i = ∑ i, P.alpha k i * P.yB B i :=
    Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _
  rw [e]

lemma basicDir_hat (hB : P.toLP.IsBasis B) {j : Fin n} (hj : j ∉ B) :
    P.inducedLP.basicDir (hat B) (Fin.castSucc j) = P.dirHat B j := by
  have hjS : Fin.castSucc j ∉ hat B := by simpa using hj
  refine (((LP.identities_main _ _ (isBasis_hat hB) (Fin.castSucc j)).2.2 hjS).1
    (P.dirHat B j)).1 ⟨?_, dirHat_j hB hj, fun k hk hkj ↦ ?_⟩ |>.symm
  · rw [inducedLP_mulVec, acomb_dirHat hB hj, sum_dirHat, snoc_zero_zero]
  · exact dirHat_eq_zero hB hj k (by simp [hk, hkj])

lemma uS_hat (hB : P.toLP.IsBasis B) : P.uS (hat B) = P.uHat B := by
  have hS := isBasis_hat (P := P) hB
  rw [hS.eq_solOn (uS_spec hS).1 (uS_spec hS).2,
    hS.eq_solOn (x := P.uHat B) (r := Fin.snoc (α := fun _ ↦ ℝ) (P.vS (hat B)) 0)
      (by rw [inducedLP_mulVec, acomb_uHat hB, sum_uHat, vS_hat hB]; rfl) (uHat_eq_zero hB)]

lemma epsS_hat (hB : P.toLP.IsBasis B) : P.epsS (hat B) = P.eps B := by
  simp [epsS, eps, vS_hat hB, hS_hat hB, ySq, yB]

lemma isFeasibleBasis_hat (hB : P.toLP.IsFeasibleBasis B) :
    P.inducedLP.IsFeasibleBasis (hat B) :=
  ⟨isBasis_hat hB.1, by rw [basicSol_hat hB.1]; exact lamHat_nonneg hB⟩

lemma improving_hat' (hB : P.toLP.IsBasis B) :
    P.inducedLP.improving (hat B) = (P.toLP.improving B).map Fin.castSuccEmb := by
  ext k
  simp only [LP.improving, mem_filter, mem_univ, true_and, reducedCost_hat hB]
  induction k using Fin.lastCases with
  | last =>
    simp [rcHat_last, Finset.mem_map, Fin.castSucc_ne_last]
  | cast k =>
    rw [rcHat_castSucc, show Fin.castSucc k = Fin.castSuccEmb k from rfl, Finset.mem_map']
    simp

/-! ### Feasible bases of the induced LP are hats -/

lemma exists_hat_of_feasible (hP : P.IsAdmissible) {S : Finset (Fin (n + 1))}
    (hS : P.inducedLP.IsFeasibleBasis S) : ∃ B, P.toLP.IsFeasibleBasis B ∧ S = hat B := by
  classical
  obtain ⟨hac, hsum⟩ := basicSol_acomb hS.1
  have hv := hS.1.basicSol_spec.2
  set lam := P.inducedLP.basicSol S with hlam_def
  set lam' : Fin n → ℝ := fun k ↦ lam (Fin.castSucc k) with hlam'
  set x : Fin n → ℝ := (P.T : ℝ) • lam' with hx_def
  have hlam : Fin.snoc (α := fun _ ↦ ℝ) lam' (lam (Fin.last n)) = lam := Fin.snoc_init_self lam
  have hsum' : ∑ k, lam' k + lam (Fin.last n) = 1 := by
    rw [← hsum, Fin.sum_univ_castSucc]
  have hTpos := P.T_pos
  have hAx : P.toLP.A *ᵥ x = P.toLP.b := by
    funext i
    have := congrFun hac i
    rw [← hlam, acomb_snoc, hsum'] at this
    simp only [Pi.zero_apply] at this
    rw [hx_def, mulVec_smul, Pi.smul_apply, smul_eq_mul, toLP_b]
    field_simp at this ⊢
    linarith
  have hx : P.toLP.IsFeasible x :=
    ⟨hAx, fun k ↦ mul_nonneg hTpos.le (hS.2 _)⟩
  have hTb := T_bound_main P hP x hx
  have hsx : ∑ k, x k = (P.T : ℝ) * ∑ k, lam' k := by
    rw [Finset.mul_sum]; rfl
  rw [hsx] at hTb
  have hlt : ∑ k, lam' k < 1 := by
    by_contra hc
    push Not at hc
    nlinarith
  have hpos : 0 < lam (Fin.last n) := by linarith
  have hlast : Fin.last n ∈ S := by
    by_contra h; rw [hv _ h] at hpos; exact lt_irrefl 0 hpos
  set B : Finset (Fin n) := univ.filter (fun k ↦ Fin.castSucc k ∈ S) with hB_def
  have hSB : S = hat B := by
    ext k
    induction k using Fin.lastCases with
    | last => simp [hlast]
    | cast k => simp [hB_def]
  have hcard : B.card = m := by
    have h1 := card_hat B
    rw [← hSB, hS.1.1] at h1
    omega
  have hbas : P.toLP.IsBasis B := by
    refine ⟨hcard, (LP.linIndep_iff _ _).2 fun y hy0 hAy ↦ ?_⟩
    set β := Fin.snoc (α := fun _ ↦ ℝ) y (-∑ k, y k) with hβ
    have hβ0 : ∀ k ∉ S, β k = 0 := by
      rw [hSB]; exact snoc_eq_zero_of_not_mem_hat hy0
    have hAβ : P.inducedLP.A *ᵥ β = 0 := by
      rw [inducedLP_mulVec, sum_snoc, add_neg_cancel, ← snoc_zero_zero]
      congr 1
      funext i
      rw [hβ, acomb_snoc, hAy]
      simp
    have h0 := hS.1.eq_zero hβ0 hAβ
    funext k
    have := congrFun h0 (Fin.castSucc k)
    simpa [hβ] using this
  have hxB : x = P.toLP.basicSol B := hbas.eq_basicSol hAx (fun k hk ↦ by
    have : Fin.castSucc k ∉ S := by simpa [hB_def] using hk
    simp [hx_def, hlam', hv _ this])
  refine ⟨B, ⟨hbas, fun k ↦ ?_⟩, hSB⟩
  rw [← hxB]; exact hx.2 k

lemma feasible_iff (hP : P.IsAdmissible) (S : Finset (Fin (n + 1))) :
    P.inducedLP.IsFeasibleBasis S ↔ ∃ B, P.toLP.IsFeasibleBasis B ∧ S = hat B :=
  ⟨exists_hat_of_feasible hP, by rintro ⟨B, hB, rfl⟩; exact isFeasibleBasis_hat hB⟩

lemma exists_feasibleBasis (hP : P.IsAdmissible) : ∃ B, P.toLP.IsFeasibleBasis B := by
  obtain ⟨x, hx⟩ := hP.2.2.1.1
  obtain ⟨B, hB, -⟩ := LP.exists_feasibleBasis_sum_ge _ hP.2.1 hP.2.2.1 x hx
  exact ⟨B, hB⟩

lemma inducedLP_bdd (hP : P.IsAdmissible) : P.inducedLP.FeasibleSetNonemptyBounded := by
  obtain ⟨B, hB⟩ := exists_feasibleBasis hP
  have hS := isFeasibleBasis_hat hB
  refine ⟨⟨_, hS.1.basicSol_spec.1, hS.2⟩, 1, fun lam hlam j ↦ ?_⟩
  have hsum := (P.acomb_eq_of_mulVec hlam.1).2
  rw [abs_of_nonneg (hlam.2 j), ← hsum]
  exact Finset.single_le_sum (fun k _ ↦ hlam.2 k) (mem_univ j)

/-! ### Leaving labels -/

lemma leaving_unique (hP : P.IsAdmissible) (hB : P.toLP.IsFeasibleBasis B) {j : Fin n}
    (hj : j ∈ P.toLP.improving B) {i i' : Fin n} (hi : P.toLP.IsLeavingLabel B j i)
    (hi' : P.toLP.IsLeavingLabel B j i') : i = i' := by
  by_contra hne
  obtain ⟨hB', hx'⟩ := LP.pivot_spec hB hj hi
  have hi'B' : i' ∈ insert j (B.erase i) := mem_insert_of_mem (mem_erase.2 ⟨Ne.symm hne, hi'.1⟩)
  have h := hP.2.2.2 _ hB' i' hi'B'
  rw [hx'] at h
  have h1 := hi.2.2 i' hi'.1 hi'.2.1
  have h2 := hi'.2.2 i hi.1 hi.2.1
  have heq : P.toLP.basicSol B i / -P.toLP.basicDir B j i =
      P.toLP.basicSol B i' / -P.toLP.basicDir B j i' := le_antisymm h1 h2
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
  rw [heq, div_neg, neg_mul, div_mul_cancel₀ _ hi'.2.1.ne, add_neg_cancel] at h
  exact lt_irrefl 0 h

lemma leaving_hat_imp (hP : P.IsAdmissible) (hB : P.toLP.IsFeasibleBasis B) {j : Fin n}
    (hj : j ∈ P.toLP.improving B) {i' : Fin (n + 1)}
    (hi' : P.inducedLP.IsLeavingLabel (hat B) (Fin.castSucc j) i') :
    ∃ i, i' = Fin.castSucc i ∧ P.toLP.IsLeavingLabel B j i := by
  have hjB := hB.1.not_mem_of_mem_improving hj
  have hjL : Fin.castSucc j ∈ P.inducedLP.improving (hat B) := by
    rw [improving_hat' hB.1]; exact Finset.mem_map_of_mem _ hj
  have hne : i' ≠ Fin.last n := by
    rintro rfl
    have hF := (LP.pivot_spec (isFeasibleBasis_hat hB) hjL hi').1
    obtain ⟨B'', -, hB''⟩ := exists_hat_of_feasible hP hF
    have : Fin.last n ∈ insert (Fin.castSucc j) ((hat B).erase (Fin.last n)) := by
      rw [hB'']; exact last_mem_hat
    rcases Finset.mem_insert.1 this with h | h
    · exact Fin.castSucc_ne_last j h.symm
    · simp at h
  obtain ⟨i, rfl⟩ | h := Fin.eq_castSucc_or_eq_last i'
  swap; · exact absurd h hne
  refine ⟨i, rfl, ?_⟩
  obtain ⟨hi1, hi2, hi3⟩ := hi'
  rw [basicDir_hat hB.1 hjB] at hi2
  rw [basicSol_hat hB.1, basicDir_hat hB.1 hjB] at hi3
  have hT := P.T_pos
  refine ⟨castSucc_mem_hat.1 hi1, by simpa using hi2, fun k hk hdk ↦ ?_⟩
  have := hi3 (Fin.castSucc k) (castSucc_mem_hat.2 hk) (by simpa using hdk)
  simp only [lamHat, dirHat, Fin.snoc_castSucc, xB] at this
  rw [div_right_comm, div_right_comm (P.toLP.basicSol B k)] at this
  exact (div_le_div_iff_of_pos_right hT).1 this

lemma leaving_hat_iff (hP : P.IsAdmissible) (hB : P.toLP.IsFeasibleBasis B) {j : Fin n}
    (hj : j ∈ P.toLP.improving B) (i' : Fin (n + 1)) :
    P.inducedLP.IsLeavingLabel (hat B) (Fin.castSucc j) i' ↔
      ∃ i, i' = Fin.castSucc i ∧ P.toLP.IsLeavingLabel B j i := by
  refine ⟨leaving_hat_imp hP hB hj, ?_⟩
  rintro ⟨i, rfl, hi⟩
  have hjL : Fin.castSucc j ∈ P.inducedLP.improving (hat B) := by
    rw [improving_hat' hB.1]; exact Finset.mem_map_of_mem _ hj
  obtain ⟨i'', hi''⟩ := LP.exists_leavingLabel (inducedLP_bdd hP) (isFeasibleBasis_hat hB) hjL
  obtain ⟨i0, rfl, hi0⟩ := leaving_hat_imp hP hB hj hi''
  rwa [leaving_unique hP hB hj hi hi0]

/-! ### Lemma 2 (`lem:hom`) -/

theorem hom' (P : IntLP m n) (hP : P.IsAdmissible) :
    (P.inducedLP.A.rank = m + 1 ∧ P.inducedLP.FeasibleSetNonemptyBounded ∧
      ∀ S, P.inducedLP.IsFeasibleBasis S → P.inducedLP.IsNondegenerate S) ∧
    (∀ S, P.inducedLP.IsFeasibleBasis S ↔ ∃ B, P.toLP.IsFeasibleBasis B ∧ S = hat B) ∧
    (∀ B, P.toLP.IsFeasibleBasis B →
      P.inducedLP.basicSol (hat B) =
        Fin.snoc (α := fun _ ↦ ℝ) (fun k ↦ P.toLP.basicSol B k / P.T)
          ((P.T - ∑ k, P.toLP.basicSol B k) / P.T) ∧
      (P.vS (hat B) = P.toLP.dualVec B ∧ P.hS (hat B) = P.C + P.toLP.objValue B / P.T) ∧
      (∀ j : Fin n, P.inducedLP.reducedCost (hat B) (Fin.castSucc j) = P.toLP.reducedCost B j) ∧
      P.inducedLP.reducedCost (hat B) (Fin.last n) = 0) ∧
    (∀ B, P.toLP.IsFeasibleBasis B → ∀ j ∈ P.toLP.improving B,
      (∃! i, P.toLP.IsLeavingLabel B j i) ∧
      ∀ i' : Fin (n + 1), P.inducedLP.IsLeavingLabel (hat B) (Fin.castSucc j) i' ↔
        ∃ i, i' = Fin.castSucc i ∧ P.toLP.IsLeavingLabel B j i) ∧
    (∀ B j B', P.toLP.IsFeasibleBasis B →
      (P.toLP.IsPivot B j B' ↔ P.inducedLP.IsPivot (hat B) (Fin.castSucc j) (hat B'))) ∧
    ∀ f (B : ℕ → Finset (Fin n)),
      P.toLP.IsSimplexRun f B ↔ P.inducedLP.IsSimplexRun f (fun k ↦ hat (B k)) := by
  have hfeas := feasible_iff hP
  have himp : ∀ B, P.toLP.IsFeasibleBasis B →
      P.inducedLP.improving (hat B) = (P.toLP.improving B).map Fin.castSuccEmb :=
    fun B hB ↦ improving_hat' hB.1
  have hleave : ∀ B, P.toLP.IsFeasibleBasis B → ∀ j ∈ P.toLP.improving B, ∀ i' : Fin (n + 1),
      P.inducedLP.IsLeavingLabel (hat B) (Fin.castSucc j) i' ↔
        ∃ i, i' = Fin.castSucc i ∧ P.toLP.IsLeavingLabel B j i :=
    fun B hB j hj i' ↦ leaving_hat_iff hP hB hj i'
  have hpiv : ∀ B j B', P.toLP.IsFeasibleBasis B →
      (P.toLP.IsPivot B j B' ↔ P.inducedLP.IsPivot (hat B) (Fin.castSucc j) (hat B')) := by
    intro B j B' hB
    refine ⟨LP.transfer_pivot_of _ _ hfeas himp hleave, fun h ↦ ?_⟩
    obtain ⟨j0, i, hjj, hj0, hi, hS'⟩ := LP.transfer_pivot_spec _ _ himp hleave hB h
    obtain rfl := Fin.castSucc_injective _ hjj
    exact ⟨hB, hj0, hB.1.not_mem_of_mem_improving hj0, i, hi, hat_injective hS'⟩
  refine ⟨⟨?_, inducedLP_bdd hP, ?_⟩, hfeas, fun B hB ↦ ⟨basicSol_hat hB.1, ⟨vS_hat hB.1, ?_⟩,
    fun j ↦ ?_, ?_⟩, fun B hB j hj ↦ ⟨?_, hleave B hB j hj⟩, hpiv, fun f B ↦ ?_⟩
  · obtain ⟨B, hB⟩ := exists_feasibleBasis hP
    exact rank_eq_of_isBasis (isBasis_hat hB.1)
  · intro S hS i hi
    obtain ⟨B, hB, rfl⟩ := exists_hat_of_feasible hP hS
    rw [basicSol_hat hB.1]
    exact lt_of_lt_of_le (one_div_pos.2 P.H_pos) (lamHat_ge hB (hP.2.2.2 B hB) hi)
  · rw [hS_hat hB.1, hHat, LP.objValue, hB.1.objValue_eq]; rfl
  · rw [reducedCost_hat hB.1, rcHat_castSucc]
  · rw [reducedCost_hat hB.1, rcHat_last]
  · obtain ⟨i, hi⟩ := LP.exists_leavingLabel hP.2.2.1 hB hj
    exact ⟨i, hi, fun i' hi' ↦ leaving_unique hP hB hj hi' hi⟩
  · constructor
    · rintro ⟨hF, hP', hlast⟩
      refine ⟨fun k hk ↦ isFeasibleBasis_hat (hF k hk), fun k hk ↦ ?_, ?_⟩
      · obtain ⟨j, hj, hpk⟩ := hP' k hk
        refine ⟨Fin.castSucc j, ?_, (hpiv _ _ _ (hF k hk.le)).1 hpk⟩
        rw [himp _ (hF k hk.le)]; exact Finset.mem_map_of_mem _ hj
      · simp only
        rw [himp _ (hF f le_rfl), hlast, Finset.map_empty]
    · rintro ⟨hF, hP', hlast⟩
      have hF' : ∀ k ≤ f, P.toLP.IsFeasibleBasis (B k) := by
        intro k hk
        obtain ⟨B'', hB'', heq⟩ := exists_hat_of_feasible hP (hF k hk)
        rw [hat_injective heq]; exact hB''
      refine ⟨hF', fun k hk ↦ ?_, ?_⟩
      · obtain ⟨j', hj', hpk⟩ := hP' k hk
        simp only at hj' hpk
        rw [himp _ (hF' k hk.le)] at hj'
        obtain ⟨j, hj, rfl⟩ := Finset.mem_map.1 hj'
        exact ⟨j, hj, (hpiv _ _ _ (hF' k hk.le)).2 hpk⟩
      · simp only at hlast
        rw [himp _ (hF' f le_rfl), Finset.map_eq_empty] at hlast
        exact hlast

/-! ### Lemma 5 (`lem:bases-corrals`) -/

theorem bases_corrals' (P : IntLP m n) (hP : P.IsAdmissible) (S : Finset (Fin (n + 1)))
    (hS : P.inducedLP.IsFeasibleBasis S) :
    (∀ i ∈ S, 1 / (P.H : ℝ) ≤ P.inducedLP.basicSol S i) ∧
    (∀ j ∉ S, ∀ k, P.inducedLP.basicDir S j k ≠ 0 →
      1 / (P.H : ℝ) ≤ |P.inducedLP.basicDir S j k| ∧ |P.inducedLP.basicDir S j k| ≤ P.H) ∧
    (∀ i, |affineCoeffs P.atom S i - P.inducedLP.basicSol S i| = P.epsS S * |P.uS S i| ∧
      P.epsS S * |P.uS S i| ≤ 1 / (4 * m * (P.H : ℝ) ^ 3)) ∧
    IsCorral P.atom S := by
  obtain ⟨B, hB, rfl⟩ := exists_hat_of_feasible hP hS
  have hm := hP.1
  have hnd := hP.2.2.2 B hB
  rw [basicSol_hat hB.1]
  refine ⟨fun i hi ↦ lamHat_ge hB hnd hi, fun j hj k hk ↦ ?_, fun i ↦ ?_, isCorral_hat hB hnd hm⟩
  · obtain ⟨j0, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last j
    swap; · exact absurd last_mem_hat hj
    have hj0 : j0 ∉ B := by simpa using hj
    rw [basicDir_hat hB.1 hj0] at hk ⊢
    by_cases hkB : k ∈ hat B
    · exact ⟨(dirHat_bound hB.1 hj0 hkB).2 hk, (dirHat_bound hB.1 hj0 hkB).1⟩
    · by_cases hkj : k = Fin.castSucc j0
      · subst hkj
        rw [dirHat_j hB.1 hj0, abs_one]
        have hH : (1 : ℝ) ≤ P.H := by exact_mod_cast P.one_le_H
        exact ⟨by rw [div_le_one P.H_pos]; exact hH, hH⟩
      · exact absurd (dirHat_eq_zero hB.1 hj0 k (by simp [hkB, hkj])) hk
  · rw [affineCoeffs_hat hB.1 hm, lamStar, epsS_hat hB.1, uS_hat hB.1]
    refine ⟨?_, eps_mul_abs_uHat_le hB hm i⟩
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_sub_cancel_left, abs_neg, abs_mul,
      abs_of_pos (eps_pos hB hm)]

/-! ### Lemma 6 (`lem:pivot`) -/

theorem pivot' (P : IntLP m n) (hP : P.IsAdmissible) (S : Finset (Fin (n + 1)))
    (hS : P.inducedLP.IsFeasibleBasis S) (j : Fin (n + 1))
    (hj : P.inducedLP.reducedCost S j < 0) (i : Fin (n + 1))
    (hi : P.inducedLP.IsLeavingLabel S j i) :
    ¬ IsCorral P.atom (insert j S) ∧
    (∃ s', MinorCycle P.atom ⟨insert j S, affineCoeffs P.atom S⟩ s') ∧
    (∀ s', MinorCycle P.atom ⟨insert j S, affineCoeffs P.atom S⟩ s' →
      s'.S = insert j (S.erase i)) ∧
    IsCorral P.atom (insert j (S.erase i)) ∧
    ∀ S' : Finset (Fin (n + 1)), MajorCycle P.atom S j S' ↔ S' = insert j (S.erase i) := by
  obtain ⟨B, hB, rfl⟩ := exists_hat_of_feasible hP hS
  obtain ⟨j0, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last j
  swap
  · rw [reducedCost_hat hB.1, rcHat_last] at hj; exact absurd hj (lt_irrefl 0)
  have hj0 : j0 ∈ P.toLP.improving B := by
    rw [reducedCost_hat hB.1, rcHat_castSucc] at hj; simpa [LP.improving] using hj
  obtain ⟨i0, rfl, hi0⟩ := leaving_hat_imp hP hB hj0 hi
  rw [hat_insert_erase]
  exact thm_b hP hB hj0 hi0

/-! ### Lemma 10 (`lem:encoding`) -/

theorem encoding' (P : IntLP m n) (hP : P.IsAdmissible) :
    (∀ j k, ∃ z : ℤ, P.atom j k = z) ∧
    P.T ≤ ((m + 1) * P.maxEntry) ^ (36 * (m + 1) ^ 2) ∧
    P.C ≤ ((((m + 1) * P.maxEntry) ^ (36 * (m + 1) ^ 2) : ℕ) : ℤ) ∧
    P.K ≤ ((m + 1) * P.maxEntry) ^ (36 * (m + 1) ^ 2) ∧
    P.H ≤ ((m + 1) * P.maxEntry) ^ (36 * (m + 1) ^ 2) ∧
    P.N ≤ ((m + 1) * P.maxEntry) ^ (36 * (m + 1) ^ 2) ∧
    ∀ j k, |P.atom j k| ≤ (((m + 1) * P.maxEntry : ℕ) : ℝ) ^ (36 * (m + 1) ^ 2) := by
  have hm := hP.1
  have hNK := P.N_sq_mul_K_le hm
  have hK := P.one_le_K
  have hN := P.N_pos hm
  have hH := P.one_le_H
  have hT := P.one_le_T
  set Q := ((m + 1) * P.maxEntry) ^ (36 * (m + 1) ^ 2) with hQ
  have hNle : P.N ≤ P.N ^ 2 * P.K := by
    calc P.N = P.N * 1 * 1 := by ring
      _ ≤ P.N * P.N * P.K := Nat.mul_le_mul (Nat.mul_le_mul le_rfl hN) hK
      _ = P.N ^ 2 * P.K := by ring
  have hKle : P.K ≤ P.N ^ 2 * P.K := Nat.le_mul_of_pos_left _ (by positivity)
  have hH3 : 1 ≤ P.H ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hTle : P.T ≤ P.N := by
    unfold N
    calc P.T = 1 * P.T * 1 := by ring
      _ ≤ (2 * m) * P.T * P.H ^ 3 := Nat.mul_le_mul (Nat.mul_le_mul (by omega) le_rfl) hH3
  have hHle : P.H ≤ P.N := by
    unfold N
    calc P.H ≤ P.H ^ 3 := Nat.le_self_pow (by norm_num) _
      _ ≤ (2 * m * P.T) * P.H ^ 3 := Nat.le_mul_of_pos_left _ (by positivity)
  have hC : P.C ≤ (P.K : ℤ) := by
    have h1 := P.natAbs_gamma_le (Fin.last n)
    rw [gamma_last] at h1
    have h2 : P.C ≤ (P.C.natAbs : ℤ) := Int.le_natAbs
    omega
  refine ⟨P.atom_integral, by omega, ?_, by omega, by omega, by omega, P.atom_size hm⟩
  have : P.K ≤ Q := by omega
  have : (P.K : ℤ) ≤ (Q : ℤ) := by exact_mod_cast this
  omega

end IntLP


open Finset Wolfe

theorem induced_facts_main (P : IntLP m n) (S : Finset (Fin (n + 1))) (hS : P.inducedLP.IsBasis S)
    (j : Fin (n + 1)) :
    (∑ i ∈ S, P.inducedLP.basicSol S i • P.alpha i = 0 ∧
      ∑ i ∈ S, P.inducedLP.basicSol S i = 1) ∧
    (∑ i, (P.gamma i : ℝ) * P.inducedLP.basicSol S i = P.hS S ∧
      (P.inducedLP.IsFeasibleBasis S → 1 ≤ P.hS S)) ∧
    (j ∉ S → ∑ k, P.inducedLP.basicDir S j k • P.alpha k = 0 ∧
      ∑ k, P.inducedLP.basicDir S j k = 0 ∧
      ∑ k, (P.gamma k : ℝ) * P.inducedLP.basicDir S j k = P.inducedLP.reducedCost S j) :=
  IntLP.induced_facts' P S hS j

theorem encoding_main (P : IntLP m n) (hP : P.IsAdmissible) :
    (∀ j k, ∃ z : ℤ, P.atom j k = z) ∧
    P.T ≤ ((m + 1) * P.maxEntry) ^ (36 * (m + 1) ^ 2) ∧
    P.C ≤ ((((m + 1) * P.maxEntry) ^ (36 * (m + 1) ^ 2) : ℕ) : ℤ) ∧
    P.K ≤ ((m + 1) * P.maxEntry) ^ (36 * (m + 1) ^ 2) ∧
    P.H ≤ ((m + 1) * P.maxEntry) ^ (36 * (m + 1) ^ 2) ∧
    P.N ≤ ((m + 1) * P.maxEntry) ^ (36 * (m + 1) ^ 2) ∧
    ∀ j k, |P.atom j k| ≤ (((m + 1) * P.maxEntry : ℕ) : ℝ) ^ (36 * (m + 1) ^ 2) :=
  IntLP.encoding' P hP

theorem hom_main (P : IntLP m n) (hP : P.IsAdmissible) :
    (P.inducedLP.A.rank = m + 1 ∧ P.inducedLP.FeasibleSetNonemptyBounded ∧
      ∀ S, P.inducedLP.IsFeasibleBasis S → P.inducedLP.IsNondegenerate S) ∧
    (∀ S, P.inducedLP.IsFeasibleBasis S ↔ ∃ B, P.toLP.IsFeasibleBasis B ∧ S = hat B) ∧
    (∀ B, P.toLP.IsFeasibleBasis B →
      P.inducedLP.basicSol (hat B) =
        Fin.snoc (α := fun _ ↦ ℝ) (fun k ↦ P.toLP.basicSol B k / P.T)
          ((P.T - ∑ k, P.toLP.basicSol B k) / P.T) ∧
      (P.vS (hat B) = P.toLP.dualVec B ∧ P.hS (hat B) = P.C + P.toLP.objValue B / P.T) ∧
      (∀ j : Fin n, P.inducedLP.reducedCost (hat B) (Fin.castSucc j) = P.toLP.reducedCost B j) ∧
      P.inducedLP.reducedCost (hat B) (Fin.last n) = 0) ∧
    (∀ B, P.toLP.IsFeasibleBasis B → ∀ j ∈ P.toLP.improving B,
      (∃! i, P.toLP.IsLeavingLabel B j i) ∧
      ∀ i' : Fin (n + 1), P.inducedLP.IsLeavingLabel (hat B) (Fin.castSucc j) i' ↔
        ∃ i, i' = Fin.castSucc i ∧ P.toLP.IsLeavingLabel B j i) ∧
    (∀ B j B', P.toLP.IsFeasibleBasis B →
      (P.toLP.IsPivot B j B' ↔ P.inducedLP.IsPivot (hat B) (Fin.castSucc j) (hat B'))) ∧
    ∀ f (B : ℕ → Finset (Fin n)),
      P.toLP.IsSimplexRun f B ↔ P.inducedLP.IsSimplexRun f (fun k ↦ hat (B k)) :=
  IntLP.hom' P hP

theorem direction_main (P : IntLP m n) (S : Finset (Fin (n + 1))) (hS : P.inducedLP.IsBasis S)
    (j : Fin (n + 1)) (hj : j ∉ S) (w : Fin (m + 1) → ℝ) :
    P.atom j + ∑ i ∈ S, P.inducedLP.basicDir S j i • P.atom i =
      ((P.N : ℝ) * P.inducedLP.reducedCost S j) • Pi.single 0 1 ∧
    gap P.atom j w + ∑ i ∈ S, P.inducedLP.basicDir S j i * gap P.atom i w =
      (P.N : ℝ) * P.inducedLP.reducedCost S j * w 0 :=
  IntLP.direction' P S hS j hj w

theorem corral_main (P : IntLP m n) (hP : P.IsAdmissible) (S : Finset (Fin (n + 1)))
    (hS : P.inducedLP.IsBasis S) :
    (IsAffinelyIndependent P.atom S ∧
      affineCoeffs P.atom S = P.inducedLP.basicSol S - P.epsS S • P.uS S ∧
      affineMin P.atom S = Fin.cons (α := fun _ ↦ ℝ) ((P.N : ℝ) * P.sS S)
        (fun i ↦ -(P.N : ℝ) ^ 2 * P.epsS S * P.vS S i) ∧
      ∑ i, (P.gamma i : ℝ) * affineCoeffs P.atom S i = P.sS S ∧
      P.sS S = P.hS S - P.epsS S * (P.vS S ⬝ᵥ P.vS S)) ∧
    (∀ j, gap P.atom j (affineMin P.atom S) = (P.N : ℝ) ^ 2 * P.sS S * P.inducedLP.reducedCost S j) ∧
    (P.inducedLP.IsFeasibleBasis S → 0 < P.sS S) :=
  IntLP.corral' P hP S hS

theorem bases_corrals_main (P : IntLP m n) (hP : P.IsAdmissible) (S : Finset (Fin (n + 1)))
    (hS : P.inducedLP.IsFeasibleBasis S) :
    (∀ i ∈ S, 1 / (P.H : ℝ) ≤ P.inducedLP.basicSol S i) ∧
    (∀ j ∉ S, ∀ k, P.inducedLP.basicDir S j k ≠ 0 →
      1 / (P.H : ℝ) ≤ |P.inducedLP.basicDir S j k| ∧ |P.inducedLP.basicDir S j k| ≤ P.H) ∧
    (∀ i, |affineCoeffs P.atom S i - P.inducedLP.basicSol S i| = P.epsS S * |P.uS S i| ∧
      P.epsS S * |P.uS S i| ≤ 1 / (4 * m * (P.H : ℝ) ^ 3)) ∧
    IsCorral P.atom S :=
  IntLP.bases_corrals' P hP S hS

theorem pivot_main (P : IntLP m n) (hP : P.IsAdmissible) (S : Finset (Fin (n + 1)))
    (hS : P.inducedLP.IsFeasibleBasis S) (j : Fin (n + 1))
    (hj : P.inducedLP.reducedCost S j < 0) (i : Fin (n + 1))
    (hi : P.inducedLP.IsLeavingLabel S j i) :
    ¬ IsCorral P.atom (insert j S) ∧
    (∃ s', MinorCycle P.atom ⟨insert j S, affineCoeffs P.atom S⟩ s') ∧
    (∀ s', MinorCycle P.atom ⟨insert j S, affineCoeffs P.atom S⟩ s' →
      s'.S = insert j (S.erase i)) ∧
    IsCorral P.atom (insert j (S.erase i)) ∧
    ∀ S' : Finset (Fin (n + 1)), MajorCycle P.atom S j S' ↔ S' = insert j (S.erase i) :=
  IntLP.pivot' P hP S hS j hj i hi

end WolfeSimplex
