import Mathlib

/-! Uniform polynomial bounds, with natural coefficients and exponents. -/

namespace WolfeSimplex.Efficiency

/-- One pair of constants works for every input, not just one fixed LP. -/
def PolynomialBound {ι : Type} (size cost : ι → ℕ) : Prop :=
  ∃ c e : ℕ, ∀ i, cost i ≤ c * (1 + size i) ^ e

namespace PolynomialBound
variable {ι κ : Type} {s f g : ι → ℕ}

theorem const (s : ι → ℕ) (c : ℕ) : PolynomialBound s (fun _ ↦ c) := by
  exact ⟨c, 0, by simp⟩

theorem input (s : ι → ℕ) : PolynomialBound s s := by
  exact ⟨1, 1, by simp⟩

theorem mono (hf : PolynomialBound s f) (h : ∀ i, g i ≤ f i) : PolynomialBound s g := by
  obtain ⟨c, e, hc⟩ := hf
  exact ⟨c, e, fun i ↦ (h i).trans (hc i)⟩

theorem add (hf : PolynomialBound s f) (hg : PolynomialBound s g) :
    PolynomialBound s (fun i ↦ f i + g i) := by
  obtain ⟨c, e, hc⟩ := hf
  obtain ⟨d, k, hd⟩ := hg
  refine ⟨c + d, e + k, fun i ↦ ?_⟩
  have hbase : 1 ≤ 1 + s i := by omega
  have he : (1 + s i) ^ e ≤ (1 + s i) ^ (e + k) :=
    Nat.pow_le_pow_right hbase (by omega)
  have hk : (1 + s i) ^ k ≤ (1 + s i) ^ (e + k) :=
    Nat.pow_le_pow_right hbase (by omega)
  calc f i + g i ≤ c * (1 + s i) ^ e + d * (1 + s i) ^ k := Nat.add_le_add (hc i) (hd i)
       _ ≤ c * (1 + s i) ^ (e + k) + d * (1 + s i) ^ (e + k) := by gcongr
       _ = _ := by ring

theorem mul (hf : PolynomialBound s f) (hg : PolynomialBound s g) :
    PolynomialBound s (fun i ↦ f i * g i) := by
  obtain ⟨c, e, hc⟩ := hf
  obtain ⟨d, k, hd⟩ := hg
  refine ⟨c * d, e + k, fun i ↦ ?_⟩
  calc f i * g i ≤ (c * (1 + s i) ^ e) * (d * (1 + s i) ^ k) :=
          Nat.mul_le_mul (hc i) (hd i)
       _ = _ := by rw [pow_add]; ring

theorem square (hf : PolynomialBound s f) : PolynomialBound s (fun i ↦ (f i) ^ 2) := by
  simpa only [pow_two] using hf.mul hf

/-- Polynomial bounds compose, including the target's binary input length. -/
theorem comp {t : κ → ℕ} {h : κ → ℕ} (hh : PolynomialBound t h)
    (r : ι → κ) (hr : PolynomialBound s (fun i ↦ t (r i))) :
    PolynomialBound s (fun i ↦ h (r i)) := by
  obtain ⟨c, e, hc⟩ := hh
  obtain ⟨d, k, hd⟩ := hr
  refine ⟨c * (1 + d) ^ e, k * e, fun i ↦ ?_⟩
  have hpow : 1 ≤ (1 + s i) ^ k := Nat.one_le_pow _ _ (by omega)
  have ht : 1 + t (r i) ≤ (1 + d) * (1 + s i) ^ k := by
    have := hd i
    nlinarith
  calc h (r i) ≤ c * (1 + t (r i)) ^ e := hc (r i)
       _ ≤ c * ((1 + d) * (1 + s i) ^ k) ^ e := by gcongr
       _ = _ := by rw [mul_pow, ← pow_mul]; ring

end PolynomialBound
end WolfeSimplex.Efficiency
