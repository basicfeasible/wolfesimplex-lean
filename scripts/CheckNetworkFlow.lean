import WolfeSimplex.Proofs.NetworkFlow
import WolfeSimplex.AxiomAudit

/-!
Capacity-slack regression cases on two parallel arcs with total flow two.
The second arc has capacity one, so it reaches the opposite bound before the
tree arc reaches a bound. Reversing its cost tests entry from the upper bound.
These are concrete bounded-variable pivots, including the flow update, rather
than assumptions that a corresponding standard-form pivot exists.
-/

namespace WolfeSimplex.NetworkFlowCheck

open Finset Matrix BoundedLP

private def flowLP (cost : ℝ) : BoundedLP 1 2 where
  A := !![1, 1]
  b := ![2]
  c := ![0, cost]
  u := ![4, 1]

private def lowerState : BoundedLP.State 2 :=
  ⟨{0}, ∅, ![2, 0]⟩

private def upperState : BoundedLP.State 2 :=
  ⟨{0}, {1}, ![1, 1]⟩

private lemma tree_basis (cost : ℝ) :
    (flowLP cost).toLP.IsBasis ({0} : Finset (Fin 2)) := by
  refine ⟨by decide, (LP.linIndep_iff _ _).2 ?_⟩
  intro x hoff hAx
  have h1 := hoff 1 (by decide)
  have h0 := congrFun hAx 0
  simp [flowLP, BoundedLP.toLP, mulVec, dotProduct, Fin.sum_univ_succ, h1] at h0
  funext j
  fin_cases j <;> simp_all

private lemma lower_state (cost : ℝ) : (flowLP cost).IsState lowerState := by
  refine ⟨tree_basis cost, by decide, ⟨?_, ?_⟩, ?_⟩
  · ext i
    fin_cases i
    norm_num [flowLP, lowerState, mulVec, dotProduct, Fin.sum_univ_succ]
  · intro j
    fin_cases j <;> norm_num [flowLP, lowerState]
  · intro j hj
    fin_cases j <;> simp_all [lowerState]

private lemma upper_state (cost : ℝ) : (flowLP cost).IsState upperState := by
  refine ⟨tree_basis cost, by decide, ⟨?_, ?_⟩, ?_⟩
  · ext i
    fin_cases i
    norm_num [flowLP, upperState, mulVec, dotProduct, Fin.sum_univ_succ]
  · intro j
    fin_cases j <;> norm_num [flowLP, upperState]
  · intro j hj
    fin_cases j <;> simp_all [upperState, flowLP]

private lemma basic_direction (cost : ℝ) :
    (flowLP cost).toLP.basicDir ({0} : Finset (Fin 2)) 1 = ![-1, 1] := by
  symm
  apply (tree_basis cost).eq_basicDir (by decide)
  refine ⟨?_, by norm_num, ?_⟩
  · ext i
    fin_cases i
    norm_num [flowLP, BoundedLP.toLP, mulVec, dotProduct,
      Fin.sum_univ_succ]
  · intro j hj hne
    fin_cases j <;> simp_all

private lemma basic_cost (cost : ℝ) :
    (flowLP cost).toLP.reducedCost ({0} : Finset (Fin 2)) 1 = cost := by
  rw [← (tree_basis cost).cost_basicDir (j := 1) (by decide), basic_direction]
  simp [flowLP, BoundedLP.toLP, dotProduct, Fin.sum_univ_succ]

private lemma lower_direction (cost : ℝ) :
    (flowLP cost).direction lowerState 1 = ![-1, 1] := by
  simp [BoundedLP.direction, BoundedLP.sign, lowerState, basic_direction]

private lemma upper_direction (cost : ℝ) :
    (flowLP cost).direction upperState 1 = ![1, -1] := by
  funext j
  fin_cases j <;>
    simp [BoundedLP.direction, BoundedLP.sign, upperState, basic_direction]

private lemma lower_improves : (flowLP (-1)).IsImproving lowerState 1 := by
  refine ⟨by decide, ?_⟩
  norm_num [BoundedLP.reducedCost, BoundedLP.sign, lowerState, basic_cost]

private lemma upper_improves : (flowLP 1).IsImproving upperState 1 := by
  refine ⟨by decide, ?_⟩
  norm_num [BoundedLP.reducedCost, BoundedLP.sign, upperState, basic_cost]

private lemma lower_choice : (flowLP (-1)).IsDantzigChoice lowerState 1 := by
  refine ⟨lower_improves, ?_⟩
  intro k hk
  have hk1 : k = 1 := by
    fin_cases k <;> simp_all [BoundedLP.IsImproving, lowerState]
  subst k
  exact le_rfl

private lemma upper_choice : (flowLP 1).IsDantzigChoice upperState 1 := by
  refine ⟨upper_improves, ?_⟩
  intro k hk
  have hk1 : k = 1 := by
    fin_cases k <;> simp_all [BoundedLP.IsImproving, upperState]
  subst k
  exact le_rfl

/-- The entering lower arc immediately leaves at its upper bound. -/
private lemma lower_flip : (flowLP (-1)).IsPivot lowerState 1 upperState := by
  refine ⟨lower_improves, upper 1, ?_, by decide, ?_⟩
  · rw [BoundedLP.IsLeavingBound, lower_direction]
    refine ⟨by norm_num [liftDir, upper, Fin.append, Fin.addCases], ?_⟩
    intro k hk
    fin_cases k <;>
      norm_num [liftDir, BoundedLP.lift, flowLP, lowerState, upper,
        Fin.append, Fin.addCases] at hk <;>
      norm_num [liftDir, BoundedLP.lift, flowLP, lowerState, upper,
        Fin.append, Fin.addCases]
  · rw [lower_direction]
    funext j
    fin_cases j <;>
      norm_num [BoundedLP.lift, liftDir, flowLP, lowerState, upperState, upper,
        Fin.append, Fin.addCases]

/-- Reversing the cost releases the upper bound and decreases the arc's flow. -/
private lemma upper_flip : (flowLP 1).IsPivot upperState 1 lowerState := by
  refine ⟨upper_improves, lower 1, ?_, by decide, ?_⟩
  · rw [BoundedLP.IsLeavingBound, upper_direction]
    refine ⟨by norm_num [liftDir, lower, Fin.append, Fin.addCases], ?_⟩
    intro k hk
    fin_cases k <;>
      norm_num [liftDir, BoundedLP.lift, flowLP, upperState, lower,
        Fin.append, Fin.addCases] at hk <;>
      norm_num [liftDir, BoundedLP.lift, flowLP, upperState, lower,
        Fin.append, Fin.addCases]
  · rw [upper_direction]
    funext j
    fin_cases j <;>
      norm_num [BoundedLP.lift, liftDir, flowLP, lowerState, upperState, lower,
        Fin.append, Fin.addCases]

/-- Neither pivot exchanges tree arcs: the second arc flips its bound. -/
example : lowerState.tree = upperState.tree := rfl

example : (flowLP (-1)).standard.IsPivot lowerState.basis (lowerState.entering 1)
    upperState.basis :=
  standard_pivot _ lowerState (lower_state (-1)) 1 upperState lower_flip

example : (flowLP 1).standard.IsPivot upperState.basis (upperState.entering 1)
    lowerState.basis :=
  standard_pivot _ upperState (upper_state 1) 1 lowerState upper_flip

/-- An upper arc enters through its capacity slack, with negated reduced cost. -/
example : (flowLP 1).standard.reducedCost upperState.basis (upper 1) = -1 := by
  have h := standard_reducedCost (flowLP 1) upperState (upper_state 1) 1 (by decide)
  simpa [BoundedLP.State.entering, BoundedLP.reducedCost, BoundedLP.sign,
    upperState, basic_cost] using h

example : (flowLP (-1)).standard.IsDantzigChoice lowerState.basis
    (lowerState.entering 1) :=
  (standard_dantzig_iff _ lowerState (lower_state (-1)) 1).2 lower_choice

example : (flowLP 1).standard.IsDantzigChoice upperState.basis
    (upperState.entering 1) :=
  (standard_dantzig_iff _ upperState (upper_state 1) 1).2 upper_choice

example : (flowLP 1).standard.IsNondegenerate upperState.basis := by
  apply standard_nondegenerate _ upperState (upper_state 1)
  · intro j
    fin_cases j <;> norm_num [flowLP]
  · intro j hj
    fin_cases j
    · norm_num [upperState, flowLP]
    · norm_num [upperState] at hj

end WolfeSimplex.NetworkFlowCheck

run_cmd WolfeSimplex.Audit.project
