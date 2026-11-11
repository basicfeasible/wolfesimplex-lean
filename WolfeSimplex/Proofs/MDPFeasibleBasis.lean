import WolfeSimplex.Proofs.SimplexFacts

/-! Positive-supply MDP matrices have nondegenerate feasible bases. This is
derived from their column sign pattern, not imported as a hardness premise. -/

namespace WolfeSimplex.LP
open Finset Matrix
variable {m n : ℕ} (P : LP m n)

/-- Each column belongs to one state and is nonpositive in all other rows.
A positive right-hand side forces one positive basic variable per state. -/
theorem nondegenerate_of_columnOwners (owner : Fin n → Fin m)
    (hb : ∀ i, 0 < P.b i)
    (hA : ∀ i j, i ≠ owner j → P.A i j ≤ 0)
    (B : Finset (Fin n)) (hB : P.IsFeasibleBasis B) : P.IsNondegenerate B := by
  have hex : ∀ i : Fin m, ∃ j : Fin n,
      j ∈ B ∧ owner j = i ∧ 0 < P.basicSol B j := by
    intro i
    have hs : 0 < ∑ j, P.A i j * P.basicSol B j := by
      change 0 < (P.A *ᵥ P.basicSol B) i
      rw [hB.1.basicSol_spec.1]
      exact hb i
    have hex : ∃ j, 0 < P.A i j * P.basicSol B j := by
      by_contra hn
      have hall : ∀ j, P.A i j * P.basicSol B j ≤ 0 :=
        fun j ↦ le_of_not_gt (fun h ↦ hn ⟨j, h⟩)
      have hsum : (∑ j, P.A i j * P.basicSol B j) ≤ 0 :=
        Finset.sum_nonpos (fun j _ ↦ hall j)
      exact (not_lt_of_ge hsum) hs
    obtain ⟨j, hj⟩ := hex
    have hjB : j ∈ B := by
      by_contra hn
      rw [hB.1.basicSol_spec.2 j hn, mul_zero] at hj
      exact (lt_irrefl 0) hj
    have ho : owner j = i := by
      by_contra hn
      have hp := mul_nonpos_of_nonpos_of_nonneg (hA i j (Ne.symm hn)) (hB.2 j)
      exact (not_lt_of_ge hp) hj
    have hx : 0 < P.basicSol B j := by
      by_contra hn
      have hz := le_antisymm (le_of_not_gt hn) (hB.2 j)
      rw [hz, mul_zero] at hj
      exact (lt_irrefl 0) hj
    exact ⟨j, hjB, ho, hx⟩
  choose f hfB hfo hfp using hex
  have hfinj : Function.Injective f := by
    intro i k h
    simpa only [hfo] using congrArg owner h
  have himage : univ.image f = B := by
    apply Finset.eq_of_subset_of_card_le
    · intro j hj
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
      exact hfB i
    · rw [Finset.card_image_of_injective _ hfinj, Finset.card_univ,
        Fintype.card_fin, hB.1.1]
  intro j hj
  rw [← himage, Finset.mem_image] at hj
  obtain ⟨i, _, rfl⟩ := hj
  exact hfp i

end WolfeSimplex.LP
