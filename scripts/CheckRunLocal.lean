import WolfeSimplex.Proofs.RunLocal
import WolfeSimplex.AxiomAudit

/-! A regression example outside the globally admissible theorem's scope.
The LP has the nondegenerate optimal basis `{0,1}` and a different, degenerate
feasible basis `{1,2}`. The run-local correspondence applies to the former.
-/

namespace WolfeSimplex.RunLocalCheck

open Finset Matrix Wolfe

private def lp : IntLP 2 3 where
  A := !![1, 0, 1; 0, 1, 1]
  b := ![1, 1]
  c := 0

private def start : Finset (Fin 3) := {0, 1}
private def other : Finset (Fin 3) := {1, 2}

private lemma start_basis : lp.toLP.IsBasis start := by
  refine ⟨by decide, (LP.linIndep_iff _ _).2 ?_⟩
  intro x hoff hAx
  have h2 := hoff 2 (by decide)
  have h0 := congrFun hAx 0
  have h1 := congrFun hAx 1
  simp [lp, IntLP.toLP, mulVec, dotProduct, Fin.sum_univ_succ, h2] at h0 h1
  funext j
  fin_cases j <;> simp_all

private lemma other_basis : lp.toLP.IsBasis other := by
  refine ⟨by decide, (LP.linIndep_iff _ _).2 ?_⟩
  intro x hoff hAx
  have h0 := hoff 0 (by decide)
  have hA0 := congrFun hAx 0
  have hA1 := congrFun hAx 1
  simp [lp, IntLP.toLP, mulVec, dotProduct, Fin.sum_univ_succ, h0] at hA0 hA1
  funext j
  fin_cases j <;> simp_all

private lemma start_sol : lp.toLP.basicSol start = ![1, 1, 0] := by
  symm
  apply start_basis.eq_basicSol
  · ext i
    fin_cases i <;> norm_num [lp, IntLP.toLP, mulVec, dotProduct, Fin.sum_univ_succ]
  · intro j hj
    fin_cases j <;> simp_all [start]

private lemma other_sol : lp.toLP.basicSol other = ![0, 0, 1] := by
  symm
  apply other_basis.eq_basicSol
  · ext i
    fin_cases i <;> norm_num [lp, IntLP.toLP, mulVec, dotProduct, Fin.sum_univ_succ]
  · intro j hj
    fin_cases j <;> simp_all [other]

private lemma start_feasible : lp.toLP.IsFeasibleBasis start := by
  refine ⟨start_basis, fun j ↦ ?_⟩
  rw [start_sol]
  fin_cases j <;> norm_num

private lemma other_feasible : lp.toLP.IsFeasibleBasis other := by
  refine ⟨other_basis, fun j ↦ ?_⟩
  rw [other_sol]
  fin_cases j <;> norm_num

private lemma start_nondegenerate : lp.toLP.IsNondegenerate start := by
  intro j hj
  rw [start_sol]
  fin_cases j <;> simp_all [start]

/-- The original global admissibility premise is genuinely false here. -/
example : ¬ lp.IsAdmissible := by
  intro h
  have hp := h.2.2.2 other other_feasible 1 (by decide)
  rw [other_sol] at hp
  norm_num at hp

private lemma start_optimal : lp.toLP.IsOptimalBasis start := by
  refine ⟨start_feasible, ⟨start_basis.basicSol_spec.1, start_feasible.2⟩, ?_⟩
  intro y _
  simp [lp, IntLP.toLP]

private lemma stationary_run : lp.toLP.IsSimplexRunWith lp.toLP.IsDantzigChoice 0
    (fun _ ↦ start) := by
  refine ⟨⟨fun _ _ ↦ start_feasible, fun k hk ↦ ?_⟩,
    (LP.optimal_iff start_feasible start_nondegenerate).1 start_optimal⟩
  omega

/-- The local theorem still proves an actual complete Wolfe run. -/
example : IsWolfeRunWith lp.atom (IsLinoptChoice lp.atom) 0 (fun _ ↦ hat start) :=
  IntLP.linopt_run_hat_of_nondegenerate (by decide) 0 _ stationary_run
    (fun _ _ ↦ start_nondegenerate)

/-- The cap and run-local correspondence compose for the same nonadmissible LP. -/
example : IsWolfeRunWith lp.cap.atom (IsLinoptChoice lp.cap.atom) 0
    (fun _ ↦ hat (hat start)) :=
  IntLP.capped_linopt_run_of_nondegenerate ⟨_, start_optimal.2⟩ 0 _ stationary_run
    (fun _ _ ↦ start_nondegenerate)

end WolfeSimplex.RunLocalCheck

run_cmd WolfeSimplex.Audit.project
