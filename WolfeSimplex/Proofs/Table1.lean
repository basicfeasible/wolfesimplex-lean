import WolfeSimplex.Proofs.RandomRates
import WolfeSimplex.Proofs.Corollary2Internal

/-! Quantitative entry points for every row of Table 1. The table's `n`
denotes the source LP's number of variables, not the number of target points.
The internally constructed Klee--Minty LP has `2d` variables; the statements
below expose the `Omega(2^(n/2))` inequalities directly from its exact counts.
Zadeh/Cunningham use `ExponentialBound`; the randomized rows use the explicit
fourth-root/square-root rates proved in `RandomRates`. -/
namespace WolfeSimplex.PaperCorollary2
open Wolfe Finset

theorem table1_least_index_count (d f : ℕ) (hd : 1 ≤ d) (hf : f = 2 ^ d - 1) :
    2 ^ ((2 * d) / 2) ≤ 2 * f := by
  have hp : 2 ≤ 2 ^ d := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 1 ≤ 2) hd
  rw [Nat.mul_div_cancel_left _ (by decide : 0 < 2), hf]
  omega

theorem table1_linopt_count (d f : ℕ) (hf : f + 1 = 2 ^ d + d + 1) :
    2 ^ ((2 * d) / 2) ≤ f := by
  rw [Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
  omega

/-- Table 1's least-index bound on actual Wolfe executions of the internally
proved family, with the source LP dimension `2d` made explicit. -/
theorem least_index_table1 (d : ℕ) (hd : 1 ≤ d) :
    (∃ S, IsWolfeRunWith (kleeMinty d).atom (IsLeastLabelChoice (kleeMinty d).atom Fin.val)
      (2 ^ d - 1) S ∧ S 0 = hat (basisOf (kmSlack d))) ∧
    ∀ f S, IsWolfeRunWith (kleeMinty d).atom
      (IsLeastLabelChoice (kleeMinty d).atom Fin.val) f S →
      S 0 = hat (basisOf (kmSlack d)) → 2 ^ ((2 * d) / 2) ≤ 2 * f := by
  have h := least_index d hd
  exact ⟨h.2.2.1, fun f S hS h0 ↦ table1_least_index_count d f hd (h.2.2.2 f S hS h0)⟩

/-- Table 1's linopt rate holds even from the unique shortest atom. -/
theorem linopt_table1 (d : ℕ) (hd : 1 ≤ d) :
    ∃ p : Fin (2 * d + 2) → Fin (d + 2) → ℝ,
      (∀ j k, ∃ z : ℤ, p j k = z) ∧
      ∃ k₀, (∀ j ≠ k₀, normSq (p k₀) < normSq (p j)) ∧
        (∃ f S, IsWolfeRunWith p (IsLinoptChoice p) f S ∧ S 0 = {k₀}) ∧
        ∀ f S, IsWolfeRunWith p (IsLinoptChoice p) f S → S 0 = {k₀} →
          2 ^ ((2 * d) / 2) ≤ f := by
  obtain ⟨p, hint, _, k₀, hmin, hex, hall, _⟩ := km_linopt d hd
  exact ⟨p, hint, k₀, hmin, hex,
    fun f S hS h0 ↦ table1_linopt_count d f (hall f S hS h0).1⟩

end WolfeSimplex.PaperCorollary2
