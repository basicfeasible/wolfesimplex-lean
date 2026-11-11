import WolfeSimplex.Proofs.BoundTransfers

/-!
# Corollary 2 with explicit literature premises

Source LPs may be unbounded. The cited input facts are rank, nondegeneracy,
an attained optimum, a specified feasible start, and the source iteration bound.
These are theorem arguments, never added axioms. Capping, preservation of rules,
the simplex–Wolfe correspondence and the final lower bounds are proved here.
-/

namespace WolfeSimplex.PaperCorollary2

open Finset Wolfe Transfers
variable {m n : ℕ}

/-- The structural facts cited for a source lower-bound LP. Boundedness is not
assumed: the proved cap construction supplies it. -/
structure LiteratureInput (m n : ℕ) where
  lp : IntLP m n
  rows : 1 ≤ m
  rank : lp.toLP.A.rank = m
  optimum : ∃ x, lp.toLP.IsOptimalSolution x
  nondegenerate : ∀ B, lp.toLP.IsFeasibleBasis B → lp.toLP.IsNondegenerate B
  initial : Finset (Fin n)
  feasible : lp.toLP.IsFeasibleBasis initial

namespace LiteratureInput
variable (I : LiteratureInput m n)

noncomputable def points := I.lp.cap.atom
def start := hat (hat I.initial)

theorem capped_admissible : I.lp.cap.IsAdmissible :=
  cap_admissible I.lp I.rows I.rank I.optimum I.nondegenerate

theorem capped_start : I.lp.cap.toLP.IsFeasibleBasis (hat I.initial) :=
  (cap_bases I.lp I.rows I.rank I.optimum I.nondegenerate I.initial I.feasible).1

theorem integral : ∀ j k, ∃ z : ℤ, I.points j k = z := I.lp.cap.atom_integral

theorem start_corral : IsCorral I.points I.start :=
  (PaperPath.part_a I.lp.cap I.capped_admissible _ I.capped_start).1

/-- The artificial cap and the induced slack add exactly two labels and two
coordinates. Thus the transfer preserves exponential/superpolynomial growth
when measured in the original family's number of variables. -/
theorem dimensions : (n + 1) + 1 = n + 2 ∧ (m + 1) + 1 = m + 2 := ⟨rfl, rfl⟩

theorem zadeh (L : ℕ)
    (source : ∀ f B J, I.lp.toLP.IsSimplexRunWithHist I.lp.toLP.IsZadehChoice f B J →
      B 0 = I.initial → L ≤ f) :
    ∀ f S J, IsWolfeRunWithHist I.points (IsLeastInsertedChoice I.points) f S J →
      S 0 = I.start → L ≤ f := by
  apply Transfers.zadeh_lower_bound I.lp.cap I.capped_admissible _ I.capped_start L
  intro f B' J' hB' h0
  obtain ⟨B, J, hB, hB0, _, _⟩ :=
    (cap_zadeh I.lp I.rows I.rank I.optimum I.nondegenerate I.initial I.feasible f B' J').mp
      ⟨hB', h0⟩
  exact source f B J hB hB0

theorem cunningham (j₀ : Fin n) (L : ℕ)
    (source : ∀ f B J, I.lp.toLP.IsSimplexRunWithHist
      (I.lp.toLP.IsCunninghamChoice j₀) f B J → B 0 = I.initial → L ≤ f) :
    ∀ f S J, IsWolfeRunWithHist I.points
      (IsRoundRobinChoice I.points j₀.castSucc.castSucc) f S J →
      S 0 = I.start → L ≤ f := by
  apply Transfers.cunningham_lower_bound I.lp.cap I.capped_admissible _ I.capped_start
    j₀.castSucc L
  intro f B' J' hB' h0
  obtain ⟨B, J, hB, hB0, _, _⟩ :=
    (cap_cunningham I.lp I.rows I.rank I.optimum I.nondegenerate I.initial I.feasible
      j₀ f B' J').mp ⟨hB', h0⟩
  exact source f B J hB hB0

/-- A specified source run transfers with its complete entering-label history.
This existential form preserves a cited tie-breaking convention; no claim that
all tie-breaks are slow is required. -/
theorem zadeh_run (f : ℕ) (B : ℕ → Finset (Fin n)) (J : ℕ → Fin n)
    (hB : I.lp.toLP.IsSimplexRunWithHist I.lp.toLP.IsZadehChoice f B J)
    (h0 : B 0 = I.initial) :
    IsWolfeRunWithHist I.points (IsLeastInsertedChoice I.points) f
      (fun k ↦ hat (hat (B k))) (fun k ↦ (J k).castSucc.castSucc) ∧
      hat (hat (B 0)) = I.start := by
  have hc := (cap_zadeh I.lp I.rows I.rank I.optimum I.nondegenerate
    I.initial I.feasible f (fun k ↦ hat (B k)) (fun k ↦ (J k).castSucc)).mpr
      ⟨B, J, hB, h0, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
  exact (rules_zadeh I.lp.cap I.capped_admissible (hat I.initial) I.capped_start f
    (fun k ↦ hat (hat (B k))) (fun k ↦ (J k).castSucc.castSucc)).mpr
      ⟨_, _, hc.1, hc.2, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩

theorem cunningham_run (j₀ : Fin n) (f : ℕ) (B : ℕ → Finset (Fin n)) (J : ℕ → Fin n)
    (hB : I.lp.toLP.IsSimplexRunWithHist (I.lp.toLP.IsCunninghamChoice j₀) f B J)
    (h0 : B 0 = I.initial) :
    IsWolfeRunWithHist I.points (IsRoundRobinChoice I.points j₀.castSucc.castSucc) f
      (fun k ↦ hat (hat (B k))) (fun k ↦ (J k).castSucc.castSucc) ∧
      hat (hat (B 0)) = I.start := by
  have hc := (cap_cunningham I.lp I.rows I.rank I.optimum I.nondegenerate
    I.initial I.feasible j₀ f (fun k ↦ hat (B k)) (fun k ↦ (J k).castSucc)).mpr
      ⟨B, J, hB, h0, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
  exact (rules_cunningham I.lp.cap I.capped_admissible (hat I.initial) I.capped_start
    j₀.castSucc f (fun k ↦ hat (hat (B k))) (fun k ↦ (J k).castSucc.castSucc)).mpr
      ⟨_, _, hc.1, hc.2, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩

theorem random_edge_counts (k : ℕ) :
    (Wolfe.randomRun I.points (Wolfe.randomInsertion I.points) k I.start).map steps =
      (I.lp.toLP.randomRun I.lp.toLP.randomEdge k I.initial).map steps := by
  unfold points start
  rw [Transfers.random_edge_count I.lp.cap I.capped_admissible _ I.capped_start k,
    cap_random_edge I.lp I.rows I.rank I.optimum I.nondegenerate I.initial I.feasible k,
    PMF.map_comp]
  congr 1
  funext xs
  simp

theorem random_bland_counts (k : ℕ) :
    (Wolfe.randomOrderRun I.points k I.start).map steps =
      (I.lp.toLP.randomBlandRun k I.initial).map steps := by
  unfold points start
  rw [Transfers.random_bland_count I.lp.cap I.capped_admissible _ I.capped_start k,
    cap_random_bland I.lp I.rows I.rank I.optimum I.nondegenerate I.initial I.feasible k,
    PMF.map_comp]
  congr 1
  funext xs
  simp

theorem random_edge_expected :
    expectedLength (fun k ↦ Wolfe.randomRun I.points (Wolfe.randomInsertion I.points) k I.start) =
      expectedLength (fun k ↦ I.lp.toLP.randomRun I.lp.toLP.randomEdge k I.initial) := by
  unfold expectedLength
  congr 1
  funext k
  rw [I.random_edge_counts]

theorem random_bland_expected :
    expectedLength (fun k ↦ Wolfe.randomOrderRun I.points k I.start) =
      expectedLength (fun k ↦ I.lp.toLP.randomBlandRun k I.initial) := by
  unfold expectedLength
  congr 1
  funext k
  rw [I.random_bland_counts]

end LiteratureInput

end WolfeSimplex.PaperCorollary2
