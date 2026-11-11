import Mathlib

/-!
# Cramer's rule and determinant bounds for integer systems

Used for Equation 23 (`eq:det-bound`) in the proof of Lemma 5 (`lem:bases-corrals`) and for
Lemma 8 (`lem:T-bound`). A square system is given by an integer matrix `Q` whose
rows are indexed by `ι` and columns by `κ`, two index types of the same size.
`hinj` says that `Q` (read over `ℝ`) is nonsingular.
-/

namespace WolfeSimplex

open Matrix Finset

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Hadamard-type bound `|det A| ≤ k! K^k` for an integer matrix with entries
bounded by `K`, read in `ℝ`. -/
lemma abs_det_le_real (A : Matrix ι ι ℤ) (K : ℕ) (hAK : ∀ i j, |A i j| ≤ K) :
    |(A.det : ℝ)| ≤ (((Fintype.card ι).factorial * K ^ Fintype.card ι : ℕ) : ℝ) := by
  have h := Matrix.det_le (abv := AbsoluteValue.abs) (x := (K : ℤ)) (A := A) hAK
  simp only [AbsoluteValue.abs_apply, nsmul_eq_mul] at h
  rw [← Int.cast_abs]
  exact_mod_cast h

/-- Core of Equation 23 (`eq:det-bound`) for a square integer system `A w = r` with `det A ≠ 0`. -/
lemma square_int_system_bound (A : Matrix ι ι ℤ) (hA : A.det ≠ 0)
    (K : ℕ) (hAK : ∀ i j, |A i j| ≤ K) (r : ι → ℤ) (hr : ∀ i, |r i| ≤ K)
    (w : ι → ℝ) (hw : (A.map (Int.cast : ℤ → ℝ)) *ᵥ w = fun i => (r i : ℝ)) (j : ι) :
    |w j| ≤ (((Fintype.card ι).factorial * K ^ Fintype.card ι : ℕ) : ℝ) ∧
    (w j ≠ 0 → 1 / (((Fintype.card ι).factorial * K ^ Fintype.card ι : ℕ) : ℝ) ≤ |w j|) := by
  set B : Matrix ι ι ℝ := A.map (Int.cast : ℤ → ℝ) with hB
  set M : ℝ := (((Fintype.card ι).factorial * K ^ Fintype.card ι : ℕ) : ℝ) with hM
  have hdet : (A.det : ℝ) = B.det := Int.cast_det A
  have h1 : B.det • w = B.cramer (fun i => (r i : ℝ)) := by
    rw [cramer_eq_adjugate_mulVec, ← hw, mulVec_mulVec, adjugate_mul, smul_mulVec, one_mulVec]
  have hupd : B.updateCol j (fun i => (r i : ℝ)) = (A.updateCol j r).map (Int.cast : ℤ → ℝ) := by
    ext a b
    by_cases hb : b = j
    · subst hb; simp [B]
    · simp [B, hb]
  have key : (A.det : ℝ) * w j = ((A.updateCol j r).det : ℝ) := by
    have h2 := congrFun h1 j
    rw [Pi.smul_apply, smul_eq_mul, cramer_apply, hupd, ← Int.cast_det] at h2
    rw [h2, Int.cast_det]
  have hAK' : ∀ a b, |A.updateCol j r a b| ≤ K := by
    intro a b
    by_cases hb : b = j
    · subst hb; simp [hr]
    · simp [hb, hAK]
  have hNM := abs_det_le_real (A.updateCol j r) K hAK'
  have hDM := abs_det_le_real A K hAK
  have hD1 : (1 : ℝ) ≤ |(A.det : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hA
  have hkey : |w j| * |(A.det : ℝ)| = |((A.updateCol j r).det : ℝ)| := by
    rw [← abs_mul, mul_comm, key]
  refine ⟨?_, ?_⟩
  · nlinarith [abs_nonneg (w j)]
  · intro hw0
    have hN : (A.updateCol j r).det ≠ 0 := by
      intro h0
      rw [h0, Int.cast_zero] at key
      rcases mul_eq_zero.mp key with h | h
      · exact hA (by exact_mod_cast h)
      · exact hw0 h
    have hN1 : (1 : ℝ) ≤ |((A.updateCol j r).det : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hN
    have hMpos : 0 < M := by linarith
    rw [div_le_iff₀ hMpos]
    nlinarith [abs_nonneg (w j)]

/-- Reindexing the columns of `Q` along `e : κ ≃ ι` gives a square matrix. -/
def sq (e : κ ≃ ι) (Q : Matrix ι κ ℤ) : Matrix ι ι ℤ := fun i i' => Q i (e.symm i')

omit [DecidableEq κ] in
lemma sq_det_ne_zero (e : κ ≃ ι) (Q : Matrix ι κ ℤ)
    (hinj : ∀ z : κ → ℝ, (∀ i, ∑ c, (Q i c : ℝ) * z c = 0) → z = 0) :
    (sq e Q).det ≠ 0 := by
  intro h
  obtain ⟨v, hv0, hv⟩ := exists_mulVec_eq_zero_iff.mpr h
  apply hv0
  have hz := hinj (fun c => (v (e c) : ℝ)) (by
    intro i
    have hi := congrFun hv i
    simp only [mulVec, dotProduct, sq, Pi.zero_apply] at hi
    rw [← Equiv.sum_comp e.symm]
    simp only [Equiv.apply_symm_apply]
    exact_mod_cast hi)
  funext i'
  have := congrFun hz (e.symm i')
  simpa using this

omit [DecidableEq ι] [DecidableEq κ] in
lemma sq_mulVec (e : κ ≃ ι) (Q : Matrix ι κ ℤ) (z : κ → ℝ) :
    ((sq e Q).map (Int.cast : ℤ → ℝ)) *ᵥ (z ∘ e.symm) = fun i => ∑ c, (Q i c : ℝ) * z c := by
  funext i
  simp only [mulVec, dotProduct, sq, map_apply, Function.comp_apply]
  exact Equiv.sum_comp e.symm (fun c => (Q i c : ℝ) * z c)

/-- Equation 23 (`eq:det-bound`): every coordinate of the solution of a nonsingular integer
system `Q z = r` with entries and right-hand side bounded by `K` has absolute
value at most `k! K^k`, and at least `1/(k! K^k)` if it is nonzero
(`k` = size of the system). -/
theorem int_system_bound (hcard : Fintype.card κ = Fintype.card ι)
    (Q : Matrix ι κ ℤ)
    (hinj : ∀ z : κ → ℝ, (∀ i, ∑ c, (Q i c : ℝ) * z c = 0) → z = 0)
    (K : ℕ) (hQK : ∀ i c, |Q i c| ≤ K) (r : ι → ℤ) (hr : ∀ i, |r i| ≤ K)
    (z : κ → ℝ) (hz : ∀ i, ∑ c, (Q i c : ℝ) * z c = r i) (l : κ) :
    |z l| ≤ (((Fintype.card ι).factorial * K ^ Fintype.card ι : ℕ) : ℝ) ∧
    (z l ≠ 0 → 1 / (((Fintype.card ι).factorial * K ^ Fintype.card ι : ℕ) : ℝ) ≤ |z l|) := by
  let e : κ ≃ ι := Fintype.equivOfCardEq hcard
  have h := square_int_system_bound (sq e Q) (sq_det_ne_zero e Q hinj) K
    (fun i i' => hQK i (e.symm i')) r hr (z ∘ e.symm)
    (by rw [sq_mulVec]; funext i; exact hz i) (e l)
  simpa using h

/-- The same bounds for the transposed system `Qᵀ z = r`. -/
theorem int_system_bound_transpose (hcard : Fintype.card κ = Fintype.card ι)
    (Q : Matrix ι κ ℤ)
    (hinj : ∀ z : κ → ℝ, (∀ i, ∑ c, (Q i c : ℝ) * z c = 0) → z = 0)
    (K : ℕ) (hQK : ∀ i c, |Q i c| ≤ K) (r : κ → ℤ) (hr : ∀ c, |r c| ≤ K)
    (z : ι → ℝ) (hz : ∀ c, ∑ i, (Q i c : ℝ) * z i = r c) (l : ι) :
    |z l| ≤ (((Fintype.card ι).factorial * K ^ Fintype.card ι : ℕ) : ℝ) ∧
    (z l ≠ 0 → 1 / (((Fintype.card ι).factorial * K ^ Fintype.card ι : ℕ) : ℝ) ≤ |z l|) := by
  let e : κ ≃ ι := Fintype.equivOfCardEq hcard
  have hA : (sq e Q)ᵀ.det ≠ 0 := by
    rw [det_transpose]; exact sq_det_ne_zero e Q hinj
  exact square_int_system_bound (sq e Q)ᵀ hA K (fun i' i => hQK i (e.symm i'))
    (r ∘ e.symm) (fun i' => hr (e.symm i')) z
    (by funext i'; simp only [mulVec, dotProduct, sq, map_apply, transpose_apply,
          Function.comp_apply]; exact hz (e.symm i')) l

/-- A real right-hand side: `|z_l| ≤ (∑_i |r_i|) · k! K^k` (the entries of `Q⁻¹`
are bounded by `k! K^k`). -/
theorem real_system_bound (hcard : Fintype.card κ = Fintype.card ι)
    (Q : Matrix ι κ ℤ)
    (hinj : ∀ z : κ → ℝ, (∀ i, ∑ c, (Q i c : ℝ) * z c = 0) → z = 0)
    (K : ℕ) (hK : 1 ≤ K) (hQK : ∀ i c, |Q i c| ≤ K) (r : ι → ℝ)
    (z : κ → ℝ) (hz : ∀ i, ∑ c, (Q i c : ℝ) * z c = r i) (l : κ) :
    |z l| ≤ (∑ i, |r i|) * (((Fintype.card ι).factorial * K ^ Fintype.card ι : ℕ) : ℝ) := by
  let e : κ ≃ ι := Fintype.equivOfCardEq hcard
  set A := sq e Q
  set B : Matrix ι ι ℝ := A.map (Int.cast : ℤ → ℝ) with hB
  set M : ℝ := (((Fintype.card ι).factorial * K ^ Fintype.card ι : ℕ) : ℝ) with hM
  have hA : A.det ≠ 0 := sq_det_ne_zero e Q hinj
  have hunit : IsUnit B.det := by
    rw [hB, ← Int.cast_det]; exact isUnit_iff_ne_zero.mpr (by exact_mod_cast hA)
  have hw : B *ᵥ (z ∘ e.symm) = r := by
    rw [hB, sq_mulVec]; funext i; exact hz i
  have hw' : z ∘ e.symm = B⁻¹ *ᵥ r := by
    rw [← hw, mulVec_mulVec, nonsing_inv_mul B hunit, one_mulVec]
  have hzl : z l = ∑ i, B⁻¹ (e l) i * r i := by
    have := congrFun hw' (e l)
    simpa [mulVec, dotProduct] using this
  have hentry : ∀ i, |B⁻¹ (e l) i| ≤ M := by
    intro i
    have h := square_int_system_bound A hA K (fun a b => hQK a (e.symm b))
      (Pi.single i 1) (by
        intro a
        by_cases ha : a = i
        · subst ha; simp; exact_mod_cast hK
        · simp [ha])
      (B⁻¹ *ᵥ Pi.single i 1) (by
        rw [mulVec_mulVec, mul_nonsing_inv B hunit, one_mulVec]
        funext a
        by_cases ha : a = i
        · subst ha; simp
        · simp [ha]) (e l)
    rw [hM]; simpa [mulVec_single_one] using h.1
  rw [hzl, Finset.sum_mul]
  refine (abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul, mul_comm (|r i|)]
  exact mul_le_mul_of_nonneg_right (hentry i) (abs_nonneg _)

end WolfeSimplex
