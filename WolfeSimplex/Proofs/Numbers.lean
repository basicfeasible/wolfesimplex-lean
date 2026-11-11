import WolfeSimplex.Defs.Induced

/-!
# The numbers `U, T, C, K, H, N` and the atoms: integrality and size

Lemma 10 (`lem:encoding`) (with an explicit size bound instead of "polynomial time")
and elementary facts about the numbers of Equation 4 (`eq:T`), Equation 6 (`eq:gamma`), Equation
17 (`eq:scale`).
-/

namespace WolfeSimplex.IntLP

open Finset

variable {m n : ℕ} (P : IntLP m n)

theorem one_le_U : 1 ≤ P.U := by
  unfold U; exact le_max_left _ _

theorem one_le_T : 1 ≤ P.T := by
  unfold T; omega

theorem one_le_K : 1 ≤ P.K := by
  unfold K
  refine le_trans ?_ (Finset.le_sup (f := fun j : Fin (n + 1) ↦
    max (P.gamma j).natAbs (max (univ.sup fun i : Fin m ↦ (P.scaledAlpha j i).natAbs) 1))
    (mem_univ 0))
  exact le_trans (le_max_right _ _) (le_max_right _ _)

theorem one_le_H : 1 ≤ P.H := by
  unfold H
  have := P.one_le_K
  apply Nat.one_le_pow
  positivity

theorem N_pos (hm : 1 ≤ m) : 0 < P.N := by
  unfold N
  have := P.one_le_T
  have := P.one_le_H
  exact Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (pow_pos (by omega) _)

/-- Helper: the `natAbs` of `γ_j` is at most `K`. -/
theorem natAbs_gamma_le (j : Fin (n + 1)) : (P.gamma j).natAbs ≤ P.K := by
  unfold K
  refine le_trans ?_ (Finset.le_sup (f := fun j : Fin (n + 1) ↦
    max (P.gamma j).natAbs (max (univ.sup fun i : Fin m ↦ (P.scaledAlpha j i).natAbs) 1))
    (mem_univ j))
  exact le_max_left _ _

/-- Helper: the `natAbs` of `(T α_j)_i` is at most `K`. -/
theorem natAbs_scaledAlpha_le (j : Fin (n + 1)) (i : Fin m) :
    (P.scaledAlpha j i).natAbs ≤ P.K := by
  unfold K
  refine le_trans ?_ (Finset.le_sup (f := fun j : Fin (n + 1) ↦
    max (P.gamma j).natAbs (max (univ.sup fun i : Fin m ↦ (P.scaledAlpha j i).natAbs) 1))
    (mem_univ j))
  refine le_trans ?_ (le_max_right _ _)
  refine le_trans ?_ (le_max_left _ _)
  exact Finset.le_sup (f := fun i : Fin m ↦ (P.scaledAlpha j i).natAbs) (mem_univ i)

/-- `|γ_j| ≤ K`. -/
theorem abs_gamma_le (j : Fin (n + 1)) : |P.gamma j| ≤ P.K := by
  rw [Int.abs_eq_natAbs]
  exact_mod_cast P.natAbs_gamma_le j

/-- `|(T α_j)_i| ≤ K`. -/
theorem abs_scaledAlpha_le (j : Fin (n + 1)) (i : Fin m) : |P.scaledAlpha j i| ≤ P.K := by
  rw [Int.abs_eq_natAbs]
  exact_mod_cast P.natAbs_scaledAlpha_le j i

/-- Helper: `|c_j| ≤ C - 1`. -/
theorem natAbs_c_le (j : Fin n) :
    (P.c j).natAbs ≤ univ.sup fun j : Fin n ↦ (P.c j).natAbs :=
  Finset.le_sup (f := fun j : Fin n ↦ (P.c j).natAbs) (mem_univ j)

/-- `γ_j ≥ 1`. -/
theorem one_le_gamma (j : Fin (n + 1)) : 1 ≤ P.gamma j := by
  induction j using Fin.lastCases with
  | last =>
    simp only [gamma, Fin.snoc_last, C]
    omega
  | cast j =>
    simp only [gamma, Fin.snoc_castSucc, C]
    have h := P.natAbs_c_le j
    omega

/-- `T α_j` is the integer vector `scaledAlpha j`. -/
theorem T_mul_alpha (j : Fin (n + 1)) (i : Fin m) :
    (P.T : ℝ) * P.alpha j i = P.scaledAlpha j i := by
  have hT : (P.T : ℝ) ≠ 0 := by
    have := P.one_le_T
    exact_mod_cast (show P.T ≠ 0 by omega)
  induction j using Fin.lastCases with
  | last =>
    simp only [alpha, scaledAlpha, Fin.snoc_last]
    push_cast
    field_simp
  | cast j =>
    simp only [alpha, scaledAlpha, Fin.snoc_castSucc]
    push_cast
    field_simp

/-- The determinant bound of the proof of Lemma 5 (`lem:bases-corrals`):
`(m+1)! K^{m+1} ≤ H`. -/
theorem factorial_mul_K_pow_le_H : (m + 1).factorial * P.K ^ (m + 1) ≤ P.H := by
  unfold H
  rw [mul_pow, ← pow_mul]
  apply Nat.mul_le_mul (Nat.factorial_le_pow _)
  exact Nat.pow_le_pow_right P.one_le_K (by omega)

/-- The determinant bound of the proof of Lemma 8 (`lem:T-bound`): `m · m! U^m < T / 2`,
stated as `2 m (m! U^m) < T`. -/
theorem two_mul_factorial_lt_T : 2 * m * (m.factorial * P.U ^ m) < P.T := by
  unfold T
  rw [mul_pow]
  apply Nat.lt_succ_of_le
  apply Nat.mul_le_mul_left
  exact Nat.mul_le_mul_right _ (Nat.factorial_le_pow _)

/-- Helper: `|A_ij| ≤ U` for `natAbs`. -/
theorem natAbs_A_le (i : Fin m) (j : Fin n) : (P.A i j).natAbs ≤ P.U := by
  unfold U
  refine le_trans ?_ (le_max_right _ _)
  refine le_trans ?_ (le_max_left _ _)
  exact Finset.le_sup (f := fun ij : Fin m × Fin n ↦ (P.A ij.1 ij.2).natAbs) (mem_univ (i, j))

/-- Helper: `|b_i| ≤ U` for `natAbs`. -/
theorem natAbs_b_le (i : Fin m) : (P.b i).natAbs ≤ P.U := by
  unfold U
  refine le_trans ?_ (le_max_right _ _)
  refine le_trans ?_ (le_max_right _ _)
  exact Finset.le_sup (f := fun i : Fin m ↦ (P.b i).natAbs) (mem_univ i)

/-- Every entry of `A` and `b` has absolute value at most `U`. -/
theorem abs_A_le (i : Fin m) (j : Fin n) : |P.A i j| ≤ P.U := by
  rw [Int.abs_eq_natAbs]
  exact_mod_cast P.natAbs_A_le i j

theorem abs_b_le (i : Fin m) : |P.b i| ≤ P.U := by
  rw [Int.abs_eq_natAbs]
  exact_mod_cast P.natAbs_b_le i

/-- Helper: coordinate `i+1` of the atom `p_j` is `N² (α_j)_i`. -/
theorem atom_succ (j : Fin (n + 1)) (i : Fin m) :
    P.atom j i.succ = (P.N : ℝ) ^ 2 * P.alpha j i := by
  simp [atom]

/-- Helper: coordinate `0` of the atom `p_j` is `N γ_j`. -/
theorem atom_zero (j : Fin (n + 1)) :
    P.atom j 0 = (P.N : ℝ) * P.gamma j := by
  simp [atom]

/-- Helper: `N² (α_j)_i = N · 2m H³ · (T α_j)_i`. -/
theorem N_sq_mul_alpha (j : Fin (n + 1)) (i : Fin m) :
    (P.N : ℝ) ^ 2 * P.alpha j i = ((P.N * (2 * m * P.H ^ 3) : ℕ) : ℝ) * P.scaledAlpha j i := by
  rw [← T_mul_alpha]
  simp only [N]
  push_cast
  ring

/-- Lemma 10 (`lem:encoding`), integrality: the atoms are integer vectors. -/
theorem atom_integral : ∀ j k, ∃ z : ℤ, P.atom j k = z := by
  intro j k
  induction k using Fin.cases with
  | zero => exact ⟨P.N * P.gamma j, by rw [atom_zero]; push_cast; ring⟩
  | succ i =>
    exact ⟨(P.N * (2 * m * P.H ^ 3) : ℕ) * P.scaledAlpha j i, by
      rw [atom_succ, N_sq_mul_alpha]; push_cast; ring⟩

/-- Helper: `2 ≤ W`. -/
theorem two_le_maxEntry : 2 ≤ P.maxEntry := le_max_left _ _

/-- Helper: `U ≤ W`. -/
theorem U_le_maxEntry : P.U ≤ P.maxEntry := by
  unfold U maxEntry
  apply max_le
  · exact le_trans (by norm_num) (le_max_left _ _)
  · exact le_trans (le_max_left _ _) (le_max_right _ _)

/-- Helper: `max_j |c_j| ≤ W`. -/
theorem sup_c_le_maxEntry : (univ.sup fun j : Fin n ↦ (P.c j).natAbs) ≤ P.maxEntry := by
  unfold maxEntry
  exact le_trans (le_max_right _ _) (le_max_right _ _)

/-- Helper: `|γ_j| ≤ 1 + 2W`. -/
theorem natAbs_gamma_le_maxEntry (j : Fin (n + 1)) :
    (P.gamma j).natAbs ≤ 1 + 2 * P.maxEntry := by
  have hs := P.sup_c_le_maxEntry
  induction j using Fin.lastCases with
  | last =>
    simp only [gamma, Fin.snoc_last, C]
    omega
  | cast j =>
    simp only [gamma, Fin.snoc_castSucc, C]
    have h := P.natAbs_c_le j
    omega

/-- Helper: `|(T α_j)_i| ≤ T U + U`. -/
theorem natAbs_scaledAlpha_le_TU (j : Fin (n + 1)) (i : Fin m) :
    (P.scaledAlpha j i).natAbs ≤ P.T * P.U + P.U := by
  have hb := P.natAbs_b_le i
  induction j using Fin.lastCases with
  | last =>
    simp only [scaledAlpha, Fin.snoc_last, Int.natAbs_neg]
    omega
  | cast j =>
    simp only [scaledAlpha, Fin.snoc_castSucc]
    have ha := P.natAbs_A_le i j
    have h1 := Int.natAbs_sub_le ((P.T : ℤ) * P.A i j) (P.b i)
    rw [Int.natAbs_mul, Int.natAbs_natCast] at h1
    have h2 : P.T * (P.A i j).natAbs ≤ P.T * P.U := Nat.mul_le_mul_left _ ha
    omega

/-- Helper: with `Q = (m+1) W`, `T ≤ Q^{m+1}` (for `m ≥ 1`). -/
theorem T_le_Q_pow (hm : 1 ≤ m) : P.T ≤ ((m + 1) * P.maxEntry) ^ (m + 1) := by
  have hW := P.two_le_maxEntry
  have hU := P.U_le_maxEntry
  set W := P.maxEntry
  have h1 : m * P.U ≤ (m + 1) * W := Nat.mul_le_mul (by omega) hU
  have h2 : (m * P.U) ^ m ≤ ((m + 1) * W) ^ m := Nat.pow_le_pow_left h1 m
  have h3 : 1 ≤ ((m + 1) * W) ^ m := Nat.one_le_pow _ _ (by positivity)
  have h4 : 2 * m + 1 ≤ (m + 1) * W := by nlinarith
  unfold T
  calc 2 * m * (m * P.U) ^ m + 1 ≤ 2 * m * ((m + 1) * W) ^ m + ((m + 1) * W) ^ m := by
        gcongr
    _ = (2 * m + 1) * ((m + 1) * W) ^ m := by ring
    _ ≤ ((m + 1) * W) * ((m + 1) * W) ^ m := by gcongr
    _ = ((m + 1) * W) ^ (m + 1) := by ring

/-- Helper: `3 ≤ T` (for `m ≥ 1`). -/
theorem three_le_T (hm : 1 ≤ m) : 3 ≤ P.T := by
  have hU := P.one_le_U
  have h : 1 ≤ (m * P.U) ^ m := Nat.one_le_pow _ _ (by positivity)
  unfold T
  nlinarith

/-- Helper: `K ≤ T Q` (for `m ≥ 1`). -/
theorem K_le_TQ (hm : 1 ≤ m) : P.K ≤ P.T * ((m + 1) * P.maxEntry) := by
  have hW := P.two_le_maxEntry
  have hU := P.U_le_maxEntry
  have hT := P.three_le_T hm
  have hQ : 2 * P.maxEntry ≤ (m + 1) * P.maxEntry := by nlinarith
  unfold K
  apply Finset.sup_le
  intro j _
  apply max_le
  · have := P.natAbs_gamma_le_maxEntry j
    nlinarith
  apply max_le
  · apply Finset.sup_le
    intro i _
    have := P.natAbs_scaledAlpha_le_TU j i
    have h5 : P.T * P.U + P.U ≤ P.T * P.maxEntry + P.maxEntry := by
      have := Nat.mul_le_mul_left P.T hU
      omega
    nlinarith
  · nlinarith

/-- Helper: `N² K ≤ Q^{36 (m+1)²}` with `Q = (m+1) W` (for `m ≥ 1`). -/
theorem N_sq_mul_K_le (hm : 1 ≤ m) :
    P.N ^ 2 * P.K ≤ ((m + 1) * P.maxEntry) ^ (36 * (m + 1) ^ 2) := by
  have hW := P.two_le_maxEntry
  have hTQ := P.T_le_Q_pow hm
  have hKTQ := P.K_le_TQ hm
  set Q := (m + 1) * P.maxEntry with hQdef
  clear_value Q
  have hQ1 : 1 ≤ Q := by rw [hQdef]; nlinarith
  have hmQ : 2 * m ≤ Q := by rw [hQdef]; nlinarith
  have hm1Q : m + 1 ≤ Q := by rw [hQdef]; nlinarith
  have hK : P.K ≤ Q ^ (m + 2) := by
    calc P.K ≤ P.T * Q := hKTQ
      _ ≤ Q ^ (m + 1) * Q := Nat.mul_le_mul_right _ hTQ
      _ = Q ^ (m + 2) := by ring
  have hH : P.H ≤ Q ^ ((2 * m + 5) * (m + 1)) := by
    unfold H
    calc ((m + 1) * P.K ^ 2) ^ (m + 1) ≤ (Q * (Q ^ (m + 2)) ^ 2) ^ (m + 1) := by gcongr
      _ = Q ^ ((2 * m + 5) * (m + 1)) := by ring
  have hN : P.N ≤ Q ^ (1 + (m + 1) + 3 * ((2 * m + 5) * (m + 1))) := by
    unfold N
    calc 2 * m * P.T * P.H ^ 3 ≤ Q * Q ^ (m + 1) * (Q ^ ((2 * m + 5) * (m + 1))) ^ 3 := by
          gcongr
      _ = Q ^ (1 + (m + 1) + 3 * ((2 * m + 5) * (m + 1))) := by ring
  calc P.N ^ 2 * P.K ≤ (Q ^ (1 + (m + 1) + 3 * ((2 * m + 5) * (m + 1)))) ^ 2 * Q ^ (m + 2) := by
        gcongr
    _ = Q ^ (2 * (1 + (m + 1) + 3 * ((2 * m + 5) * (m + 1))) + (m + 2)) := by ring
    _ ≤ Q ^ (36 * (m + 1) ^ 2) := Nat.pow_le_pow_right hQ1 (by nlinarith)

/-- Lemma 10 (`lem:encoding`), size: every coordinate of an atom has absolute value at
most `((m+1) W)^{36 (m+1)²}`. -/
theorem atom_size (hm : 1 ≤ m) :
    ∀ j k, |P.atom j k| ≤ (((m + 1) * P.maxEntry : ℕ) : ℝ) ^ (36 * (m + 1) ^ 2) := by
  intro j k
  have hNK := P.N_sq_mul_K_le hm
  have hN := P.N_pos hm
  have hT := P.one_le_T
  have hTr : (1 : ℝ) ≤ P.T := by exact_mod_cast hT
  have hK : (0 : ℝ) ≤ P.K := by positivity
  have hNr : (1 : ℝ) ≤ P.N := by exact_mod_cast hN
  have hNK' : ((P.N : ℝ) ^ 2 * P.K) ≤ (((m + 1) * P.maxEntry : ℕ) : ℝ) ^ (36 * (m + 1) ^ 2) := by
    exact_mod_cast hNK
  refine le_trans ?_ hNK'
  induction k using Fin.cases with
  | zero =>
    rw [atom_zero, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ P.N)]
    have hg : |(P.gamma j : ℝ)| ≤ P.K := by exact_mod_cast P.abs_gamma_le j
    calc (P.N : ℝ) * |(P.gamma j : ℝ)| ≤ P.N * P.K := by gcongr
      _ = 1 * (P.N * P.K) := by ring
      _ ≤ P.N * (P.N * P.K) := by gcongr
      _ = (P.N : ℝ) ^ 2 * P.K := by ring
  | succ i =>
    rw [atom_succ, ← mul_div_cancel_left₀ (P.alpha j i) (by positivity : (P.T : ℝ) ≠ 0),
      T_mul_alpha, abs_mul, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (P.N : ℝ) ^ 2),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ P.T)]
    have hs : |(P.scaledAlpha j i : ℝ)| ≤ P.K := by exact_mod_cast P.abs_scaledAlpha_le j i
    gcongr
    calc |(P.scaledAlpha j i : ℝ)| / P.T ≤ |(P.scaledAlpha j i : ℝ)| / 1 := by gcongr
      _ ≤ P.K := by rw [div_one]; exact hs

end WolfeSimplex.IntLP
