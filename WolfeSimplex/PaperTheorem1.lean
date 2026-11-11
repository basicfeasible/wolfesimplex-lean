import WolfeSimplex.Proofs.PaperPath
import WolfeSimplex.Proofs.BitSize

/-!
# Theorem 1 for readers of the paper

Read the statement below together with `Defs/Simplex`, `Defs/Wolfe` and
`Defs/Induced`. Other local definitions do not occur in its statement.
The proof is composed in `Proofs/PaperPath`, following the numbered paper lemmas.
The construction clause gives integrality and signed binary length. The separate
resource certificate is in `Construction/Budget.lean`; see `docs/REVIEW.md` for scope.
-/

namespace WolfeSimplex.Paper

open Finset Wolfe

/-- The mathematical correspondence in Theorem 1, with an explicit bit-length
bound in place of the construction-time assertion. A run of length `f` has
`f` major cycles (pivots) and `f + 1` corrals (bases). -/
theorem theorem1 {m n : ℕ} (P : IntLP m n) (hP : P.IsAdmissible) :
    (∀ j k, ∃ z : ℤ, P.atom j k = z ∧
      1 + Nat.size z.natAbs ≤
        1 + 36 * (m + 1) ^ 2 * Nat.size ((m + 1) * P.maxEntry)) ∧
    (∀ B, P.toLP.IsFeasibleBasis B →
      IsCorral P.atom (hat B) ∧
      improving P.atom (affineMin P.atom (hat B)) =
        (P.toLP.improving B).map Fin.castSuccEmb ∧
      ∃ κ : ℝ, 0 < κ ∧
        (∀ j : Fin n, gap P.atom j.castSucc (affineMin P.atom (hat B)) =
          κ * P.toLP.reducedCost B j) ∧
        gap P.atom (Fin.last n) (affineMin P.atom (hat B)) = 0) ∧
    (∀ B, P.toLP.IsFeasibleBasis B → ∀ j, j ∈ P.toLP.improving B →
      ∀ i, P.toLP.IsLeavingLabel B j i →
      ¬ IsCorral P.atom (insert j.castSucc (hat B)) ∧
      (∃ s', MinorCycle P.atom
        ⟨insert j.castSucc (hat B), affineCoeffs P.atom (hat B)⟩ s') ∧
      (∀ s', MinorCycle P.atom
        ⟨insert j.castSucc (hat B), affineCoeffs P.atom (hat B)⟩ s' →
        s'.S = hat (insert j (B.erase i))) ∧
      IsCorral P.atom (hat (insert j (B.erase i))) ∧
      ∀ S', MajorCycle P.atom (hat B) j.castSucc S' ↔
        S' = hat (insert j (B.erase i))) ∧
    (∀ B₀, P.toLP.IsFeasibleBasis B₀ → ∀ f S,
      (IsWolfeRun P.atom f S ∧ S 0 = hat B₀) ↔
        ∃ B : ℕ → Finset (Fin n), P.toLP.IsSimplexRun f B ∧ B 0 = B₀ ∧
          ∀ k ≤ f, S k = hat (B k)) ∧
    (∀ B, P.toLP.IsFeasibleBasis B →
      ((improving P.atom (affineMin P.atom (hat B)) = ∅ ∧
        IsMinNormPoint P.atom (affineMin P.atom (hat B))) ↔ P.toLP.IsOptimalBasis B)) := by
  exact ⟨P.atom_bitLength hP, PaperPath.part_a P hP, PaperPath.part_b P hP,
    PaperPath.part_c P hP, PaperPath.part_d P hP⟩

end WolfeSimplex.Paper
