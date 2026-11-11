import WolfeSimplex.Efficiency.Corollary1
import WolfeSimplex.Proofs.HistoryRuns
import WolfeSimplex.Proofs.BoundTransfers

/-!
# Corollary 1 in the paper's iteration-count formulation

Rules may depend on the complete inserted-label history. A bound applies to
all partial runs, so it also prevents arbitrarily long nonterminating runs.
The separate machine theorem addresses complete procedure costs.
-/
namespace WolfeSimplex.Efficiency
open Wolfe Finset

abbrev InsertionRule := (i : Target) → List (Fin i.N) → Finset (Fin i.N) → Fin i.N → Prop
abbrev PivotRule := (i : Source) → List (Fin i.n) → Finset (Fin i.n) → Fin i.n → Prop

def inducedRule (R : InsertionRule) : PivotRule := fun i hist B j ↦
  R (reduce i) (hist.map Fin.castSucc) (hat B) j.castSucc

def RuleIterationBound (R : InsertionRule) (size : Target → ℕ) : Prop :=
  ∃ c e : ℕ, ∀ i f S J,
    IsPartialWolfeRunWithHist (realPoints i.points) (R i) f S J →
      S 0 = support i.initial → f ≤ c * (1 + size i) ^ e

def PivotIterationBound (R : PivotRule) (size : Source → ℕ) : Prop :=
  ∃ c e : ℕ, ∀ i f B J, i.lp.toLP.IsPartialSimplexRunWithHist (R i) f B J →
    B 0 = support i.initial → f ≤ c * (1 + size i) ^ e

theorem iteration_transfer (R : InsertionRule) (s : Source → ℕ) (t : Target → ℕ)
    (hr : PolynomialBound s (fun i ↦ t (reduce i))) (h : RuleIterationBound R t) :
    PivotIterationBound (inducedRule R) s := by
  obtain ⟨c, e, hc⟩ := h
  obtain ⟨d, k, hd⟩ := hr
  refine ⟨c * (1 + d) ^ e, k * e, fun i f B J hB h0 ↦ ?_⟩
  have hw := (IntLP.partialRunHist_hat_iff (P := i.lp) i.admissible (R (reduce i))
    (inducedRule R i) (fun _ _ _ _ ↦ Iff.rfl) (support i.initial) i.feasible f
    (fun k ↦ hat (B k)) (fun k ↦ (J k).castSucc)).mpr
      ⟨B, J, hB, h0, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
  have hf : f ≤ c * (1 + t (reduce i)) ^ e := by
    apply hc (reduce i) f (fun k ↦ hat (B k)) (fun k ↦ (J k).castSucc)
    · simpa only [reduce, realPoints_atoms] using hw.1
    · simpa only [reduce, support_start] using hw.2
  have hp : 1 ≤ (1 + s i) ^ k := Nat.one_le_pow _ _ (by omega)
  have ht : 1 + t (reduce i) ≤ (1 + d) * (1 + s i) ^ k := by nlinarith [hd i]
  calc f ≤ c * (1 + t (reduce i)) ^ e := hf
       _ ≤ c * ((1 + d) * (1 + s i) ^ k) ^ e := by gcongr
       _ = _ := by rw [mul_pow, ← pow_mul]; ring

/-- Polynomial major-cycle bounds give polynomial pivot bounds, with one
induced history-dependent rule for both size notions. -/
theorem corollary1_iterations (R : InsertionRule) :
    (RuleIterationBound R targetSize → PivotIterationBound (inducedRule R) sourceSize) ∧
    (RuleIterationBound R targetDimension → PivotIterationBound (inducedRule R) sourceDimension) :=
  ⟨iteration_transfer R _ _ reduction_input_size, iteration_transfer R _ _ reduction_dimension⟩

/-- A genuine insertion rule, able to choose whenever an improvement exists,
induces a genuine pivot rule with the same property at every feasible basis. -/
theorem inducedRule_total (R : InsertionRule)
    (ht : ∀ i hist S, IsCorral (realPoints i.points) S →
      (improving (realPoints i.points)
        (affineMin (realPoints i.points) S)).Nonempty →
      ∃ j ∈ improving (realPoints i.points)
        (affineMin (realPoints i.points) S), R i hist S j) :
    ∀ i hist B, i.lp.toLP.IsFeasibleBasis B → (i.lp.toLP.improving B).Nonempty →
      ∃ j ∈ i.lp.toLP.improving B, inducedRule R i hist B j := by
  intro i hist
  apply Transfers.induced_choice_total i.lp i.admissible
  intro S hS hΓ
  have h := ht (reduce i) (hist.map Fin.castSucc) S
  simp only [reduce, realPoints_atoms] at h
  exact h hS hΓ

/-- A rule can select an improving label at every nonterminal corral. -/
def InsertionTotal (R : InsertionRule) : Prop :=
  ∀ i hist S, IsCorral (realPoints i.points) S →
    (improving (realPoints i.points) (affineMin (realPoints i.points) S)).Nonempty →
    ∃ j ∈ improving (realPoints i.points) (affineMin (realPoints i.points) S), R i hist S j

def PivotTotal (R : PivotRule) : Prop :=
  ∀ i hist B, i.lp.toLP.IsFeasibleBasis B → (i.lp.toLP.improving B).Nonempty →
    ∃ j ∈ i.lp.toLP.improving B, R i hist B j

/-- Corollary 1 for a genuine rule: both its ability to proceed and its
polynomial iteration guarantees transfer to the same induced pivot rule. -/
theorem corollary1_rule (R : InsertionRule) (hR : InsertionTotal R) :
    PivotTotal (inducedRule R) ∧
    (RuleIterationBound R targetSize → PivotIterationBound (inducedRule R) sourceSize) ∧
    (RuleIterationBound R targetDimension → PivotIterationBound (inducedRule R) sourceDimension) :=
  ⟨inducedRule_total R hR, corollary1_iterations R⟩

end WolfeSimplex.Efficiency
