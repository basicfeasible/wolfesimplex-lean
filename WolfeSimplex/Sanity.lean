import WolfeSimplex.Defs.Induced

/-!
# Sanity checks (not part of the trusted statements)

Small examples showing that the hypotheses of the main results can be satisfied,
so the main results are not vacuously true.
-/

namespace WolfeSimplex.Sanity

open Finset Matrix

/-- The LP `min 0 · x₁ subject to x₁ = 1, x₁ ≥ 0` (one constraint, one variable). -/
def tiny : IntLP 1 1 where
  A := 1
  b := fun _ ↦ 1
  c := fun _ ↦ 0

lemma tiny_feasible_iff (x : Fin 1 → ℝ) : tiny.toLP.IsFeasible x ↔ x 0 = 1 := by
  constructor
  · rintro ⟨h, -⟩
    have := congrFun h 0
    simpa [tiny, IntLP.toLP, mulVec, dotProduct] using this
  · intro h
    refine ⟨?_, fun j ↦ by fin_cases j; simp [h]⟩
    funext i; fin_cases i
    simp [tiny, IntLP.toLP, mulVec, dotProduct, h]

/-- The tiny LP is admissible: the hypotheses of the main results can be met. -/
theorem tiny_admissible : tiny.IsAdmissible := by
  refine ⟨le_rfl, ?_, ⟨⟨fun _ ↦ 1, (tiny_feasible_iff _).2 rfl⟩, 1, ?_⟩, ?_⟩
  · have : tiny.toLP.A = 1 := by
      ext i j; fin_cases i; fin_cases j; simp [tiny, IntLP.toLP]
    rw [this, Matrix.rank_one]; simp
  · intro x hx j
    fin_cases j; simp [(tiny_feasible_iff x).1 hx]
  · intro B hB i hi
    have hex : ∃ x, tiny.toLP.IsBasicSolutionOf B x := by
      refine ⟨fun _ ↦ 1, ?_, ?_⟩
      · funext k; fin_cases k
        simp [tiny, IntLP.toLP, mulVec, dotProduct]
      · intro j hj; exact absurd (Subsingleton.elim i j ▸ hi) hj
    have hs := Classical.epsilon_spec hex
    have h0 := congrFun hs.1 0
    fin_cases i
    have : tiny.toLP.basicSol B 0 = 1 := by
      simpa [tiny, IntLP.toLP, mulVec, dotProduct, LP.basicSol] using h0
    simp [this]

end WolfeSimplex.Sanity
