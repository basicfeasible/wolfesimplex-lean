import WolfeSimplex.Proofs.Corollary2Growth

/-! The internally proved part of Corollary 2. Linopt and minnorm, including
shortest-point starts, are `km_linopt` and `km_minnorm`. Here the Bland family is
assembled into actual least-index Wolfe runs, and the quantitative counts are
related to the number of points. No literature premise is used in these proofs. -/
namespace WolfeSimplex.PaperCorollary2
open Wolfe Finset

/-- Actual exponentially long least-index runs, rather than only a conditional
transfer of a possible source lower bound. Every complete run has this length. -/
theorem least_index (n : ℕ) (hn : 1 ≤ n) :
    (∀ j k, ∃ z : ℤ, (kleeMinty n).atom j k = z) ∧
    IsCorral (kleeMinty n).atom (hat (basisOf (kmSlack n))) ∧
    (∃ S, IsWolfeRunWith (kleeMinty n).atom (IsLeastLabelChoice (kleeMinty n).atom Fin.val)
      (2 ^ n - 1) S ∧ S 0 = hat (basisOf (kmSlack n))) ∧
    (∀ f S, IsWolfeRunWith (kleeMinty n).atom
      (IsLeastLabelChoice (kleeMinty n).atom Fin.val) f S →
      S 0 = hat (basisOf (kmSlack n)) → f = 2 ^ n - 1) := by
  obtain ⟨hP, hB₀⟩ := km_admissible n hn
  have hk := km_bland n hn
  refine ⟨(kleeMinty n).atom_integral,
    (PaperPath.part_a _ hP _ hB₀).1, ?_, ?_⟩
  · obtain ⟨f, B, hB, h0⟩ := hk.1
    have hf := hk.2.1 f B hB h0
    have hw := (rules_bland _ hP _ hB₀ Fin.val f (fun k ↦ hat (B k))).mpr
      ⟨B, by simpa using hB, h0, fun _ _ ↦ rfl⟩
    exact ⟨_, by simpa only [hf] using hw⟩
  · intro f S hS h0
    obtain ⟨B, hB, hB0, _⟩ := (rules_bland _ hP _ hB₀ Fin.val f S).mp ⟨hS, h0⟩
    exact hk.2.1 f B (by simpa using hB) hB0

/-- The least-index count is exponential in its `2n+1` points. -/
theorem least_index_growth :
    ExponentialBound (fun r ↦ 2 * (r + 1) + 1) (fun r ↦ 2 ^ (r + 1) - 1) := by
  refine ⟨4, 2, by decide, fun r ↦ ?_⟩
  have hd : (2 * (r + 1) + 1) / 4 ≤ r + 1 := by omega
  have hp : 2 ≤ 2 ^ (r + 1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : 1 ≤ r + 1)
  calc 2 ^ ((2 * (r + 1) + 1) / 4) ≤ 2 ^ (r + 1) := Nat.pow_le_pow_right (by decide) hd
       _ ≤ _ := by
         change 2 ^ (r + 1) ≤ 2 * (2 ^ (r + 1) - 1)
         omega

/-- The exact insertion count proved for linopt/minnorm from the shortest point
is exponential in their `2n+2` points. -/
theorem shortest_start_growth :
    ExponentialBound (fun r ↦ 2 * (r + 1) + 2) (fun r ↦ 2 ^ (r + 1) + (r + 1)) := by
  refine ⟨4, 1, by decide, fun r ↦ ?_⟩
  have hd : (2 * (r + 1) + 2) / 4 ≤ r + 1 := by omega
  calc 2 ^ ((2 * (r + 1) + 2) / 4) ≤ 2 ^ (r + 1) := Nat.pow_le_pow_right (by decide) hd
       _ ≤ _ := by
         change 2 ^ (r + 1) ≤ 1 * (2 ^ (r + 1) + (r + 1))
         omega

end WolfeSimplex.PaperCorollary2
