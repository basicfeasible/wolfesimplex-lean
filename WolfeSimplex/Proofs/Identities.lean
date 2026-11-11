import WolfeSimplex.Proofs.SimplexFacts

/-!
# Lemma 7 (`lem:identities`)

Assembled from `Proofs/SimplexFacts.lean`.
-/

namespace WolfeSimplex.LP

open Finset Matrix

variable {m n : ℕ} (P : LP m n)

theorem identities_main (B : Finset (Fin n)) (hB : P.IsBasis B) (j : Fin n) :
    (∀ i ∈ B, P.reducedCost B i = 0) ∧
    ((∀ x, P.IsBasicSolutionOf B x ↔ x = P.basicSol B) ∧
      P.objValue B = P.dualVec B ⬝ᵥ P.b) ∧
    (j ∉ B → (∀ d, P.IsBasicDirOf B j d ↔ d = P.basicDir B j) ∧
      P.c ⬝ᵥ P.basicDir B j = P.reducedCost B j) := by
  refine ⟨fun i hi ↦ hB.reducedCost_of_mem hi, ⟨fun x ↦ ⟨fun h ↦ hB.eq_basicSol h.1 h.2,
    fun h ↦ h ▸ hB.basicSol_spec⟩, hB.objValue_eq⟩, fun hj ↦ ⟨fun d ↦ ⟨fun h ↦ ?_,
    fun h ↦ h ▸ hB.basicDir_spec hj⟩, hB.cost_basicDir hj⟩⟩
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := hB.basicDir_spec hj
  have : d - P.basicDir B j = 0 := hB.eq_zero
    (fun k hk ↦ by
      by_cases hkj : k = j
      · subst hkj; simp [h2, h2']
      · simp [h3 k hk hkj, h3' k hk hkj])
    (by rw [mulVec_sub, h1, h1', sub_self])
  exact sub_eq_zero.1 this

end WolfeSimplex.LP
