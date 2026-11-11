import WolfeSimplex.Proofs.Corollary2Growth

/-!
# The four cited families in Corollary 2

Each theorem accepts its own rational source family. The cited results are
premises about those source LPs (DFH23 for Zadeh, AF17 for Cunningham,
FHZ11/Han12 for Random-Edge, FHZ14 for Random-Bland). Integerization, the cap,
rule/history transport and growth after the two-label increase are proved.
Nothing requires one LP family to be slow for all four rules.
-/
namespace WolfeSimplex.PaperCorollary2
open Finset Wolfe Transfers

/-- Target family with an actual corresponding corral and integral coordinates. -/
structure IntegralFamily (m n : ℕ → ℕ) where
  points : ∀ r, Fin (n r + 2) → Fin (m r + 2) → ℝ
  start : ∀ r, Finset (Fin (n r + 2))
  integral : ∀ r j k, ∃ z : ℤ, points r j k = z
  corral : ∀ r, IsCorral (points r) (start r)

private noncomputable def integerFamily {m n : ℕ → ℕ}
    (R : ∀ r, RationalInput (m r) (n r)) : ∀ r, LiteratureInput (m r) (n r) :=
  fun r ↦ Classical.choose (integerize (R r))

private def integerFamily_spec {m n : ℕ → ℕ}
    (R : ∀ r, RationalInput (m r) (n r)) (r : ℕ) :=
  Classical.choose_spec (integerize (R r))

private noncomputable def targetFamily {m n : ℕ → ℕ}
    (R : ∀ r, RationalInput (m r) (n r)) : IntegralFamily m n where
  points r := (integerFamily R r).points
  start r := (integerFamily R r).start
  integral r := (integerFamily R r).integral
  corral r := (integerFamily R r).start_corral

/-- A witnessed exponentially long Zadeh family yields witnessed exponentially
long least-inserted runs, with the same lengths and corresponding histories. -/
theorem zadeh_family {m n f : ℕ → ℕ} (R : ∀ r, RationalInput (m r) (n r))
    (unbounded : ∀ r, r ≤ n r)
    (source : ∀ r, ∃ B J, (R r).lp.IsSimplexRunWithHist (R r).lp.IsZadehChoice (f r) B J ∧
      B 0 = (R r).initial) (growth : ExponentialBound n f) :
    ∃ T : IntegralFamily m n, (∀ r, r ≤ n r + 2) ∧
      ExponentialBound (fun r ↦ n r + 2) f ∧
      ∀ r, ∃ S J, IsWolfeRunWithHist (T.points r)
        (IsLeastInsertedChoice (T.points r)) (f r) S J ∧ S 0 = T.start r := by
  refine ⟨targetFamily R, fun r ↦ (unbounded r).trans (by omega),
    exponential_add_two growth, fun r ↦ ?_⟩
  obtain ⟨B, J, hB, h0⟩ := source r
  have hs := integerFamily_spec R r
  have hi := (hs.2.1 (f r) B J).mpr hB
  have h0' : B 0 = (integerFamily R r).initial := h0.trans hs.1.symm
  exact ⟨_, _, (integerFamily R r).zadeh_run (f r) B J hi h0'⟩

/-- Cunningham's cited family may have a different dimension and start. -/
theorem cunningham_family {m n f : ℕ → ℕ} (R : ∀ r, RationalInput (m r) (n r))
    (j₀ : ∀ r, Fin (n r)) (unbounded : ∀ r, r ≤ n r)
    (source : ∀ r, ∃ B J, (R r).lp.IsSimplexRunWithHist
      ((R r).lp.IsCunninghamChoice (j₀ r)) (f r) B J ∧ B 0 = (R r).initial)
    (growth : ExponentialBound n f) :
    ∃ T : IntegralFamily m n, (∀ r, r ≤ n r + 2) ∧
      ExponentialBound (fun r ↦ n r + 2) f ∧
      ∀ r, ∃ S J, IsWolfeRunWithHist (T.points r)
        (IsRoundRobinChoice (T.points r) (j₀ r).castSucc.castSucc) (f r) S J ∧
        S 0 = T.start r := by
  refine ⟨targetFamily R, fun r ↦ (unbounded r).trans (by omega),
    exponential_add_two growth, fun r ↦ ?_⟩
  obtain ⟨B, J, hB, h0⟩ := source r
  have hs := integerFamily_spec R r
  have hi := (hs.2.2.1 (j₀ r) (f r) B J).mpr hB
  have h0' : B 0 = (integerFamily R r).initial := h0.trans hs.1.symm
  exact ⟨_, _, (integerFamily R r).cunningham_run (j₀ r) (f r) B J hi h0'⟩

/-- Random-Edge expected counts are preserved exactly, not merely bounded. -/
theorem random_edge_family {m n : ℕ → ℕ} (R : ∀ r, RationalInput (m r) (n r))
    (unbounded : ∀ r, r ≤ n r)
    (growth : SuperpolynomialBound n (fun r ↦ expectedLength
      (fun k ↦ (R r).lp.randomRun (R r).lp.randomEdge k (R r).initial))) :
    ∃ T : IntegralFamily m n, (∀ r, r ≤ n r + 2) ∧
      (∀ r, expectedLength (fun k ↦ randomRun (T.points r)
        (randomInsertion (T.points r)) k (T.start r)) = expectedLength
          (fun k ↦ (R r).lp.randomRun (R r).lp.randomEdge k (R r).initial)) ∧
      SuperpolynomialBound (fun r ↦ n r + 2) (fun r ↦ expectedLength
        (fun k ↦ randomRun (T.points r) (randomInsertion (T.points r)) k (T.start r))) := by
  have heq (r : ℕ) : expectedLength (fun k ↦ randomRun ((targetFamily R).points r)
      (randomInsertion ((targetFamily R).points r)) k ((targetFamily R).start r)) =
      expectedLength (fun k ↦ (R r).lp.randomRun (R r).lp.randomEdge k (R r).initial) := by
    rw [show (fun k ↦ randomRun ((targetFamily R).points r)
      (randomInsertion ((targetFamily R).points r)) k ((targetFamily R).start r)) =
      (fun k ↦ randomRun (integerFamily R r).points
        (randomInsertion (integerFamily R r).points) k (integerFamily R r).start) from rfl,
      (integerFamily R r).random_edge_expected]
    apply expected_eq_of_prefix
    intro k
    have hs := integerFamily_spec R r
    dsimp only [integerFamily]
    rw [hs.1]
    exact hs.2.2.2.1 k
  refine ⟨targetFamily R, fun r ↦ (unbounded r).trans (by omega), heq, ?_⟩
  simpa only [heq] using superpolynomial_add_two growth

/-- Random-Bland uses its independently supplied cited family and order law. -/
theorem random_bland_family {m n : ℕ → ℕ} (R : ∀ r, RationalInput (m r) (n r))
    (unbounded : ∀ r, r ≤ n r)
    (growth : SuperpolynomialBound n (fun r ↦ expectedLength
      (fun k ↦ (R r).lp.randomBlandRun k (R r).initial))) :
    ∃ T : IntegralFamily m n, (∀ r, r ≤ n r + 2) ∧
      (∀ r, expectedLength (fun k ↦ randomOrderRun (T.points r) k (T.start r)) =
        expectedLength (fun k ↦ (R r).lp.randomBlandRun k (R r).initial)) ∧
      SuperpolynomialBound (fun r ↦ n r + 2) (fun r ↦ expectedLength
        (fun k ↦ randomOrderRun (T.points r) k (T.start r))) := by
  have heq (r : ℕ) : expectedLength
      (fun k ↦ randomOrderRun ((targetFamily R).points r) k ((targetFamily R).start r)) =
      expectedLength (fun k ↦ (R r).lp.randomBlandRun k (R r).initial) := by
    change expectedLength
      (fun k ↦ randomOrderRun (integerFamily R r).points k (integerFamily R r).start) = _
    rw [(integerFamily R r).random_bland_expected]
    apply expected_eq_of_prefix
    intro k
    have hs := integerFamily_spec R r
    dsimp only [integerFamily]
    rw [hs.1]
    exact hs.2.2.2.2 k
  refine ⟨targetFamily R, fun r ↦ (unbounded r).trans (by omega), heq, ?_⟩
  simpa only [heq] using superpolynomial_add_two growth

end WolfeSimplex.PaperCorollary2
