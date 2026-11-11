import WolfeSimplex.Proofs.Corollary2

namespace WolfeSimplex.PaperCorollary2

open Finset Matrix
variable {m n : ℕ}

/-- Rank follows from the supplied basis; it need not be imported as another
literature assumption after scaling. -/
theorem rank_of_basis (P : LP m n) (B : Finset (Fin n)) (hB : P.IsBasis B) :
    P.A.rank = m := by
  have hsurj : LinearMap.range P.A.mulVecLin = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro rhs
    obtain ⟨x, hx, _⟩ := hB.exists_sol rhs
    exact ⟨x, by simpa using hx⟩
  rw [Matrix.rank, hsurj, finrank_top, Module.finrank_fin_fun]

/-- Facts supplied by a cited rational LP family. The structural hypotheses are
stated on the actual source LP, before integerization and capping. -/
structure RationalInput (m n : ℕ) where
  lp : LP m n
  rationalA : ∀ i j, ∃ q : ℚ, lp.A i j = q
  rationalB : ∀ i, ∃ q : ℚ, lp.b i = q
  rationalC : ∀ j, ∃ q : ℚ, lp.c j = q
  rows : 1 ≤ m
  optimum : ∃ x, lp.IsOptimalSolution x
  nondegenerate : ∀ B, lp.IsFeasibleBasis B → lp.IsNondegenerate B
  initial : Finset (Fin n)
  feasible : lp.IsFeasibleBasis initial

/-- Integer data with exactly the same deterministic and randomized runs.
No assumption that the cited rational family is already integral is needed. -/
theorem integerize (R : RationalInput m n) :
    ∃ I : LiteratureInput m n, I.initial = R.initial ∧
      (∀ f B J, I.lp.toLP.IsSimplexRunWithHist I.lp.toLP.IsZadehChoice f B J ↔
        R.lp.IsSimplexRunWithHist R.lp.IsZadehChoice f B J) ∧
      (∀ j₀ f B J, I.lp.toLP.IsSimplexRunWithHist
        (I.lp.toLP.IsCunninghamChoice j₀) f B J ↔
        R.lp.IsSimplexRunWithHist (R.lp.IsCunninghamChoice j₀) f B J) ∧
      (∀ k, I.lp.toLP.randomRun I.lp.toLP.randomEdge k R.initial =
        R.lp.randomRun R.lp.randomEdge k R.initial) ∧
      (∀ k, I.lp.toLP.randomBlandRun k R.initial = R.lp.randomBlandRun k R.initial) := by
  obtain ⟨r, ω, Q, hr, hω, hQ⟩ := scale_integral R.lp R.rationalA R.rationalB R.rationalC
  have hstart : Q.toLP.IsFeasibleBasis R.initial := by
    rw [hQ]
    exact (R.lp.scale_isFeasibleBasis_iff hr ω _).mpr R.feasible
  have hnd : ∀ B, Q.toLP.IsFeasibleBasis B → Q.toLP.IsNondegenerate B := by
    intro B hB i hi
    rw [hQ] at hB ⊢
    have h := R.nondegenerate B ((R.lp.scale_isFeasibleBasis_iff hr ω B).mp hB) i hi
    simpa only [LP.IsNondegenerate, LP.scale_basicSol R.lp hr] using h
  have hopt : ∃ x, Q.toLP.IsOptimalSolution x := by
    obtain ⟨x, hx⟩ := R.optimum
    rw [hQ]
    refine ⟨x, (R.lp.scale_isFeasible_iff hr ω x).mpr hx.1, fun y hy ↦ ?_⟩
    have h := mul_le_mul_of_nonneg_left
      (hx.2 y ((R.lp.scale_isFeasible_iff hr ω y).mp hy)) hω.le
    simpa only [LP.scale, dotProduct, mul_assoc, Finset.mul_sum] using h
  let I : LiteratureInput m n :=
    ⟨Q, R.rows, rank_of_basis _ _ hstart.1, hopt, hnd, R.initial, hstart⟩
  refine ⟨I, rfl, ?_, ?_, ?_, ?_⟩
  · intro f B J
    change Q.toLP.IsSimplexRunWithHist _ f B J ↔ _
    rw [hQ]
    exact (scale_runs R.lp r hr ω hω).2.2.1 f B J
  · intro j₀ f B J
    change Q.toLP.IsSimplexRunWithHist _ f B J ↔ _
    rw [hQ]
    exact (scale_runs R.lp r hr ω hω).2.2.2 j₀ f B J
  · intro k
    change Q.toLP.randomRun _ k R.initial = _
    rw [hQ]
    exact (scale_random_runs R.lp r hr ω hω R.optimum R.initial R.feasible k).1
  · intro k
    change Q.toLP.randomBlandRun k R.initial = _
    rw [hQ]
    exact (scale_random_runs R.lp r hr ω hω R.optimum R.initial R.feasible k).2

/-- The expected total counts used in the literature premise are preserved by
integerization, using the identical finite-prefix distributions. -/
theorem expected_eq_of_prefix {α : Type} (p q : ℕ → PMF (List α))
    (h : ∀ k, p k = q k) : Transfers.expectedLength p = Transfers.expectedLength q := by
  congr 1
  funext k
  exact h k

end WolfeSimplex.PaperCorollary2
