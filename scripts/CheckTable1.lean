import WolfeSimplex.Proofs.RandomSource
import WolfeSimplex.AxiomAudit

/-! Exact perfect-power rate values and a rational MDP source. This fixture
derives nondegeneracy from the source sign pattern, checks concrete efficient
integerization, and connects the constructed integer arrays to the real atoms. -/
namespace WolfeSimplex.Table1Check
open PaperCorollary2 Finset Matrix Wolfe

example : stretchedRate (1/4 : ℝ) 1 0 15 = 4 := by norm_num [stretchedRate]
example : stretchedRate (1/2 : ℝ) 1 0 3 = 4 := by norm_num [stretchedRate]

example : stretchedRate (1/4 : ℝ) (1/3) 0 17 ≤ 4 := by
  have h := stretchedRate_add_two (1/4) 1 0 15 (by norm_num) (by norm_num) (by norm_num)
  norm_num [stretchedRate] at h ⊢
  exact h

#guard 2 ^ ((2 * 4) / 2) ≤ 2 * (2 ^ 4 - 1)
#guard 2 ^ ((2 * 4) / 2) ≤ 2 ^ 4 + 4

private def rat : RatLP 1 1 where
  A := !![2]
  b := ![1/3]
  c := ![-1/7]

private theorem basis : rat.toLP.IsBasis {0} := by
  refine ⟨by decide, (LP.linIndep_iff _ _).2 ?_⟩
  intro x _ hx
  have he := congrFun hx 0
  simp [rat, RatLP.toLP, mulVec, dotProduct, Fin.sum_univ_succ] at he
  funext i
  fin_cases i
  simpa using he

private theorem sol : rat.toLP.basicSol {0} = ![1/6] := by
  symm; apply basis.eq_basicSol
  · ext i; fin_cases i; norm_num [rat, RatLP.toLP, mulVec, dotProduct, Fin.sum_univ_succ]
  · intro i hi; exact (hi (by fin_cases i; simp)).elim

private theorem feasible : rat.toLP.IsFeasibleBasis {0} := by
  refine ⟨basis, fun i ↦ ?_⟩
  rw [sol]; fin_cases i; norm_num

private theorem optimum : ∃ x, rat.toLP.IsOptimalSolution x := by
  refine ⟨![1/6], ⟨?_, ?_⟩, ?_⟩
  · ext i; fin_cases i; norm_num [rat, RatLP.toLP, mulVec, dotProduct, Fin.sum_univ_succ]
  · intro i; fin_cases i; norm_num
  · intro y hy
    have he := congrFun hy.1 0
    norm_num [rat, RatLP.toLP, mulVec, dotProduct, Fin.sum_univ_succ] at he ⊢
    linarith

private def source : MDPSource 1 1 where
  lp := rat
  rows := by decide
  initial := {0}
  feasible := feasible
  optimum := optimum
  owner := fun _ ↦ 0
  positive := by intro i; fin_cases i; norm_num [rat, RatLP.toLP]
  offOwner := by intro i j h; exact (h (Subsingleton.elim _ _)).elim

#guard source.integer.lp.A 0 0 = 6
#guard source.integer.lp.b 0 = 1
#guard source.integer.lp.c 0 = -1
#guard (Construction.atoms source.integer.lp.cap)[1][1] < 0
#guard (Execution.Support.code 1).eval (Execution.Support.input source.initial) = [1, 1, 1]

example : (Execution.Support.code 1).eval (Execution.Support.input source.initial) =
    List.ofFn (fun j : Fin 3 ↦ if j ∈ source.integer.start then (1 : ℤ) else 0) :=
  source.computed_start

example : source.integer.lp.toLP.IsNondegenerate {0} :=
  source.integer_nondegenerate _ ((source.integer_feasible _).2 feasible)

example : (RatLP.Executed.run source.lp).value = source.integer.lp :=
  source.preprocessing_correct.1

example : (Execution.atomCode 2 2).eval (Execution.lpInput source.integer.lp.cap) =
    Execution.pack (fun j i ↦ (Construction.atoms source.integer.lp.cap)[j][i]) :=
  source.computed_atoms

end WolfeSimplex.Table1Check

run_cmd WolfeSimplex.Audit.project
