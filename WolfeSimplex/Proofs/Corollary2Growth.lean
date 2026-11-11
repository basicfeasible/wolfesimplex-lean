import WolfeSimplex.Proofs.Corollary2Scaling

/-! The cap and correspondence add two labels. These lemmas prove that this
change preserves the growth properties used by Corollary 2; the source growth
facts themselves are explicit literature premises. -/

namespace WolfeSimplex.PaperCorollary2

/-- A quantitative exponential lower bound in the number of source labels.
Family existence/unbounded sizes are supplied separately by the source family. -/
def ExponentialBound (size count : ℕ → ℕ) : Prop :=
  ∃ a b : ℕ, 1 ≤ a ∧ ∀ r, 2 ^ (size r / a) ≤ b * count r

/-- Eventually dominates every polynomial in the number of labels. The value
may be an expected count, hence extended nonnegative real coefficients. -/
def SuperpolynomialBound (size : ℕ → ℕ) (count : ℕ → ENNReal) : Prop :=
  ∀ c d : ℕ, ∃ R : ℕ, ∀ r ≥ R, (c * (1 + size r) ^ d : ℕ) ≤ count r

private theorem div_add_two (n a : ℕ) (ha : 1 ≤ a) : (n + 2) / a ≤ n / a + 2 := by
  have h := Nat.lt_mul_div_succ n (by omega : 0 < a)
  have h' : (n + 2) / a < n / a + 3 :=
    (Nat.div_lt_iff_lt_mul (by omega)).mpr (by nlinarith)
  omega

theorem exponential_add_two {size count : ℕ → ℕ} (h : ExponentialBound size count) :
    ExponentialBound (fun r ↦ size r + 2) count := by
  obtain ⟨a, b, ha, hb⟩ := h
  refine ⟨a, 4 * b, ha, fun r ↦ ?_⟩
  calc 2 ^ ((size r + 2) / a) ≤ 2 ^ (size r / a + 2) :=
          Nat.pow_le_pow_right (by decide) (div_add_two _ _ ha)
       _ = 4 * 2 ^ (size r / a) := by rw [pow_add]; ring
       _ ≤ 4 * (b * count r) := Nat.mul_le_mul_left _ (hb r)
       _ = _ := by ring

theorem superpolynomial_add_two {size : ℕ → ℕ} {count : ℕ → ENNReal}
    (h : SuperpolynomialBound size count) :
    SuperpolynomialBound (fun r ↦ size r + 2) count := by
  intro c d
  obtain ⟨R, hR⟩ := h (c * 3 ^ d) d
  refine ⟨R, fun r hr ↦ ?_⟩
  have hn : c * (1 + (size r + 2)) ^ d ≤ (c * 3 ^ d) * (1 + size r) ^ d := by
    calc _ ≤ c * (3 * (1 + size r)) ^ d := by gcongr; omega
         _ = _ := by rw [mul_pow]; ring
  have hn' : ((c * (1 + (size r + 2)) ^ d : ℕ) : ENNReal) ≤
      (((c * 3 ^ d) * (1 + size r) ^ d : ℕ) : ENNReal) := by exact_mod_cast hn
  exact hn'.trans (hR r hr)

end WolfeSimplex.PaperCorollary2
