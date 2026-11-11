import WolfeSimplex.Proofs.Table1
import WolfeSimplex.Proofs.MDPFeasibleBasis
import WolfeSimplex.Proofs.Corollary4Resources
import WolfeSimplex.Efficiency.InputSize
import WolfeSimplex.Execution.Support

set_option exponentiation.threshold 1024
set_option maxRecDepth 8000

/-! Source interfaces for the cited MDP lower bounds. Rational input data,
positive supplies and the published column sign pattern are source facts.
Nondegeneracy, rank, boundedness, an efficient integerization and the Wolfe
construction are proved here. The source lower-bound proofs remain external. -/
namespace WolfeSimplex.PaperCorollary2
open Finset Matrix Wolfe Transfers Efficiency
variable {m n : ℕ}

structure MDPSource (m n : ℕ) where
  lp : RatLP m n
  rows : 1 ≤ m
  initial : Finset (Fin n)
  feasible : lp.toLP.IsFeasibleBasis initial
  optimum : ∃ x, lp.toLP.IsOptimalSolution x
  owner : Fin n → Fin m
  positive : ∀ i, 0 < lp.toLP.b i
  offOwner : ∀ i j, i ≠ owner j → lp.toLP.A i j ≤ 0

namespace MDPSource
variable (S : MDPSource m n)

theorem integer_feasible (B : Finset (Fin n)) :
    S.lp.integerize.toLP.IsFeasibleBasis B ↔ S.lp.toLP.IsFeasibleBasis B := by
  rw [S.lp.integerize_eq_scale]
  exact S.lp.toLP.scale_isFeasibleBasis_iff
    (fun i ↦ Nat.cast_pos.mpr (S.lp.rowFactor_pos i)) _ B

theorem integer_nondegenerate (B : Finset (Fin n))
    (hB : S.lp.integerize.toLP.IsFeasibleBasis B) : S.lp.integerize.toLP.IsNondegenerate B :=
  (S.lp.integerize_nondegenerate B).2
    (S.lp.toLP.nondegenerate_of_columnOwners S.owner S.positive S.offOwner B
      ((S.integer_feasible B).1 hB))

theorem integer_optimum : ∃ x, S.lp.integerize.toLP.IsOptimalSolution x := by
  obtain ⟨x, hx⟩ := S.optimum
  rw [S.lp.integerize_eq_scale]
  have hr : ∀ i, (0 : ℝ) < S.lp.rowFactor i := fun i ↦ Nat.cast_pos.mpr (S.lp.rowFactor_pos i)
  have hω : (0 : ℝ) < S.lp.objectiveFactor := Nat.cast_pos.mpr S.lp.objectiveFactor_pos
  refine ⟨x, (S.lp.toLP.scale_isFeasible_iff hr _ x).2 hx.1, fun y hy ↦ ?_⟩
  have h := mul_le_mul_of_nonneg_left
    (hx.2 y ((S.lp.toLP.scale_isFeasible_iff hr _ y).1 hy)) hω.le
  simpa only [LP.scale, dotProduct, Finset.mul_sum, mul_assoc] using h

def integer : LiteratureInput m n where
  lp := S.lp.integerize
  rows := S.rows
  rank := rank_of_basis _ _ ((S.integer_feasible S.initial).2 S.feasible).1
  optimum := S.integer_optimum
  nondegenerate := S.integer_nondegenerate
  initial := S.initial
  feasible := (S.integer_feasible S.initial).2 S.feasible

theorem random_prefixes (k : ℕ) :
    S.integer.lp.toLP.randomRun S.integer.lp.toLP.randomEdge k S.initial =
      S.lp.toLP.randomRun S.lp.toLP.randomEdge k S.initial ∧
    S.integer.lp.toLP.randomBlandRun k S.initial = S.lp.toLP.randomBlandRun k S.initial := by
  change S.lp.integerize.toLP.randomRun S.lp.integerize.toLP.randomEdge k S.initial = _ ∧
    S.lp.integerize.toLP.randomBlandRun k S.initial = _
  rw [S.lp.integerize_eq_scale]
  exact scale_random_runs_main S.lp.toLP
    (fun i ↦ Nat.cast_pos.mpr (S.lp.rowFactor_pos i))
    (Nat.cast_pos.mpr S.lp.objectiveFactor_pos) S.optimum S.initial S.feasible k

theorem random_edge_expected :
    expectedLength (fun k ↦ randomRun S.integer.points (randomInsertion S.integer.points)
      k S.integer.start) =
      expectedLength (fun k ↦ S.lp.toLP.randomRun S.lp.toLP.randomEdge k S.initial) := by
  apply S.integer.random_edge_expected.trans
  apply expected_eq_of_prefix
  intro k
  exact (S.random_prefixes k).1

theorem random_bland_expected :
    expectedLength (fun k ↦ randomOrderRun S.integer.points k S.integer.start) =
      expectedLength (fun k ↦ S.lp.toLP.randomBlandRun k S.initial) := by
  apply S.integer.random_bland_expected.trans
  apply expected_eq_of_prefix
  intro k
  exact (S.random_prefixes k).2

def constructionCost : ℕ := PaperCorollary4.Resources.countCost S.lp +
  (Execution.Support.code n).bitWork (Execution.Support.input S.initial)

theorem constructionCost_bound : S.constructionCost ≤ 10 ^ 301 * (1 + S.lp.inputSize) ^ 200 := by
  have hn := S.lp.dimensions_le
  have hi := (PaperCorollary4.Resources.binary_pipelines S.lp S.rows (fun _ ↦ Fin.last n)).1
  have hs := Execution.Support.bitWork S.initial
  have hp : (n + 1) ^ 3 ≤ (1 + S.lp.inputSize) ^ 200 :=
    (Nat.pow_le_pow_left (by omega : n + 1 ≤ 1 + S.lp.inputSize) _).trans
      (Nat.pow_le_pow_right (by omega) (by decide))
  calc S.constructionCost ≤ (10 ^ 300 + 10 ^ 4) * (1 + S.lp.inputSize) ^ 200 := by
        unfold constructionCost
        rw [Nat.add_mul]
        exact Nat.add_le_add hi (hs.trans (Nat.mul_le_mul_left _ hp))
       _ ≤ _ := Nat.mul_le_mul_right _ (by norm_num)

theorem output_size : pointSize (Construction.atoms S.integer.lp.cap) ≤
    10 ^ 40 * (1 + S.lp.inputSize) ^ 25 := by
  change pointSize (Construction.atoms S.lp.integerize.cap) ≤ _
  have h := pointSize_atoms S.integer.lp.cap S.integer.capped_admissible
  change pointSize (Construction.atoms S.lp.integerize.cap) ≤
    100 * (3 * (1 + Construction.inputSize S.lp.integerize.cap)) ^ 5 at h
  have hc := PaperCorollary4.Resources.capped_inputSize S.lp S.lp.inputSize S.lp.entries_bounded
  have hd := S.lp.dimensions_le
  have hshape : m + n + S.lp.inputSize + 3 ≤ 3 * (1 + S.lp.inputSize) := by omega
  have hc' : Construction.inputSize S.lp.integerize.cap ≤
      243000 * (1 + S.lp.inputSize) ^ 5 := by
    calc _ ≤ 1000 * (3 * (1 + S.lp.inputSize)) ^ 5 :=
          hc.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hshape _))
         _ = _ := by rw [mul_pow]; ring
  have h1 : 1 + Construction.inputSize S.lp.integerize.cap ≤
      243001 * (1 + S.lp.inputSize) ^ 5 := by
    have := Nat.one_le_pow 5 (1 + S.lp.inputSize) (by omega); omega
  calc _ ≤ 100 * (3 * (243001 * (1 + S.lp.inputSize) ^ 5)) ^ 5 := h.trans (by gcongr)
       _ = (100 * (3 * 243001) ^ 5) * (1 + S.lp.inputSize) ^ 25 := by
         rw [← mul_assoc, mul_pow, ← pow_mul]; ring
       _ ≤ _ := Nat.mul_le_mul_right _ (by norm_num)

theorem data_correct (j : Fin (n + 2)) (i : Fin (m + 2)) :
    ((Construction.atoms S.integer.lp.cap)[j][i] : ℝ) = S.integer.points j i :=
  Construction.atoms_correct S.integer.lp.cap j i

theorem preprocessing_correct :
    (RatLP.Executed.run S.lp).value = S.integer.lp ∧
    (Construction.Cap.run (RatLP.Executed.run S.lp).value).value = S.integer.lp.cap := by
  have h := PaperCorollary4.Resources.programs_correct S.lp (fun _ ↦ Fin.last n)
  exact ⟨h.1, h.2.1⟩

theorem computed_atoms :
    (Execution.atomCode (m + 1) (n + 1)).eval (Execution.lpInput S.integer.lp.cap) =
      Execution.pack (fun j i ↦ (Construction.atoms S.integer.lp.cap)[j][i]) := by
  have h := Execution.atomCode_correct S.integer.lp.cap []
  simp only [List.append_nil] at h
  rw [h]
  congr 1
  funext j i
  apply Int.cast_injective (α := ℝ)
  rw [Execution.integerAtoms_correct, Construction.atoms_correct]

theorem computed_start : (Execution.Support.code n).eval (Execution.Support.input S.initial) =
    List.ofFn (fun j : Fin (n + 2) ↦ if j ∈ S.integer.start then (1 : ℤ) else 0) :=
  Execution.Support.correct S.initial

end MDPSource

private noncomputable def mdpFamily {m n : ℕ → ℕ} (S : ∀ r, MDPSource (m r) (n r)) :
    IntegralFamily m n where
  points r := (S r).integer.points
  start r := (S r).integer.start
  integral r := (S r).integer.integral
  corral r := (S r).integer.start_corral

/-- Published source encoding bounds yield polynomial target construction and
binary output length. No target size or complexity fact is a source premise. -/
theorem mdp_family_polynomial {m n : ℕ → ℕ} (S : ∀ r, MDPSource (m r) (n r))
    (sourceSize : PolynomialBound n (fun r ↦ (S r).lp.inputSize)) :
    PolynomialBound n (fun r ↦ (S r).constructionCost) ∧
    PolynomialBound n (fun r ↦ pointSize (Construction.atoms (S r).integer.lp.cap)) := by
  let X := Σ m, Σ n, MDPSource m n
  let inputSize : X → ℕ := fun x ↦ x.2.2.lp.inputSize
  let family : ℕ → X := fun r ↦ ⟨m r, n r, S r⟩
  have hw : PolynomialBound inputSize (fun x ↦ x.2.2.constructionCost) :=
    ⟨10 ^ 301, 200, fun x ↦ x.2.2.constructionCost_bound⟩
  have hs : PolynomialBound inputSize
      (fun x ↦ pointSize (Construction.atoms x.2.2.integer.lp.cap)) :=
    ⟨10 ^ 40, 25, fun x ↦ x.2.2.output_size⟩
  exact ⟨hw.comp family sourceSize, hs.comp family sourceSize⟩

/-- Quantitative random-insertion bound from the cited MDP source data. Rank,
nondegeneracy, boundedness, integerization and construction cost are discharged. -/
theorem random_edge_table1_mdp {m n : ℕ → ℕ} (S : ∀ r, MDPSource (m r) (n r))
    (unbounded : ∀ r, r ≤ n r)
    (sourceRate : StretchedExponentialBound (1/4 : ℝ) n (fun r ↦ expectedLength
      (fun k ↦ (S r).lp.toLP.randomRun (S r).lp.toLP.randomEdge k (S r).initial)))
    (sourceSize : PolynomialBound n (fun r ↦ (S r).lp.inputSize)) :
    ∃ T : IntegralFamily m n, (∀ r, r ≤ n r + 2) ∧
      (∀ r (j : Fin (n r + 2)) (i : Fin (m r + 2)),
        (((Construction.atoms (S r).integer.lp.cap)[j][i] : ℤ) : ℝ) = T.points r j i) ∧
      (∀ r, expectedLength (fun k ↦ randomRun (T.points r) (randomInsertion (T.points r))
        k (T.start r)) = expectedLength
          (fun k ↦ (S r).lp.toLP.randomRun (S r).lp.toLP.randomEdge k (S r).initial)) ∧
      StretchedExponentialBound (1/4 : ℝ) (fun r ↦ n r + 2) (fun r ↦ expectedLength
        (fun k ↦ randomRun (T.points r) (randomInsertion (T.points r)) k (T.start r))) ∧
      PolynomialBound n (fun r ↦ (S r).constructionCost) ∧
      PolynomialBound n (fun r ↦ pointSize (Construction.atoms (S r).integer.lp.cap)) := by
  have he (r : ℕ) : expectedLength (fun k ↦ randomRun ((mdpFamily S).points r)
      (randomInsertion ((mdpFamily S).points r)) k ((mdpFamily S).start r)) =
      expectedLength (fun k ↦ (S r).lp.toLP.randomRun (S r).lp.toLP.randomEdge k (S r).initial) :=
    (S r).random_edge_expected
  refine ⟨mdpFamily S, fun r ↦ (unbounded r).trans (by omega),
    fun r j i ↦ (S r).data_correct j i, he, ?_, mdp_family_polynomial S sourceSize⟩
  simpa only [he] using stretched_exponential_add_two (by norm_num : (0 : ℝ) ≤ 1/4)
    (by norm_num : (1/4 : ℝ) ≤ 1) sourceRate

/-- Quantitative random-order bound and polynomial construction from the cited
one-permutation Random-Bland source family. -/
theorem random_bland_table1_mdp {m n : ℕ → ℕ} (S : ∀ r, MDPSource (m r) (n r))
    (unbounded : ∀ r, r ≤ n r)
    (sourceRate : StretchedExponentialBound (1/2 : ℝ) n (fun r ↦ expectedLength
      (fun k ↦ (S r).lp.toLP.randomBlandRun k (S r).initial)))
    (sourceSize : PolynomialBound n (fun r ↦ (S r).lp.inputSize)) :
    ∃ T : IntegralFamily m n, (∀ r, r ≤ n r + 2) ∧
      (∀ r (j : Fin (n r + 2)) (i : Fin (m r + 2)),
        (((Construction.atoms (S r).integer.lp.cap)[j][i] : ℤ) : ℝ) = T.points r j i) ∧
      (∀ r, expectedLength (fun k ↦ randomOrderRun (T.points r) k (T.start r)) =
        expectedLength (fun k ↦ (S r).lp.toLP.randomBlandRun k (S r).initial)) ∧
      StretchedExponentialBound (1/2 : ℝ) (fun r ↦ n r + 2) (fun r ↦ expectedLength
        (fun k ↦ randomOrderRun (T.points r) k (T.start r))) ∧
      PolynomialBound n (fun r ↦ (S r).constructionCost) ∧
      PolynomialBound n (fun r ↦ pointSize (Construction.atoms (S r).integer.lp.cap)) := by
  have he (r : ℕ) : expectedLength (fun k ↦ randomOrderRun ((mdpFamily S).points r)
      k ((mdpFamily S).start r)) =
      expectedLength (fun k ↦ (S r).lp.toLP.randomBlandRun k (S r).initial) := (S r).random_bland_expected
  refine ⟨mdpFamily S, fun r ↦ (unbounded r).trans (by omega),
    fun r j i ↦ (S r).data_correct j i, he, ?_, mdp_family_polynomial S sourceSize⟩
  simpa only [he] using stretched_exponential_add_two (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ) ≤ 1) sourceRate

end WolfeSimplex.PaperCorollary2
