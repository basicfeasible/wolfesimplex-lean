import WolfeSimplex.Proofs.Corollary4
import WolfeSimplex.AxiomAudit

/-! Rational denominators, one genuine pivot, exact counting, and both query
events from the unique shortest atom under fixed-index tie breaking. -/
namespace WolfeSimplex.Corollary4Check
open Finset Matrix Wolfe PaperCorollary4

private def rat : RatLP 1 2 where
  A := !![1, 1]
  b := ![1/2]
  c := ![-1/3, 0]

#guard (RatLP.Executed.run rat).value.A 0 0 == 2
#guard (RatLP.Executed.run rat).value.b 0 == 1
#guard (RatLP.Executed.run rat).value.c 0 == -1
#guard (RatLP.Executed.run rat).operations == 17
#guard (RatLP.Executed.run rat).bookkeeping == 71
#guard (RatLP.Executed.run rat).peak == 3

private theorem basis (j : Fin 2) : rat.toLP.IsBasis {j} := by
  refine ⟨by simp, (LP.linIndep_iff _ _).2 ?_⟩
  intro x hoff hAx
  have h := congrFun hAx 0
  fin_cases j
  · have h1 := hoff 1 (by decide)
    simp [rat, RatLP.toLP, mulVec, dotProduct, Fin.sum_univ_succ, h1] at h
    funext i; fin_cases i <;> simp_all
  · have h0 := hoff 0 (by decide)
    simp [rat, RatLP.toLP, mulVec, dotProduct, Fin.sum_univ_succ, h0] at h
    funext i; fin_cases i <;> simp_all

private theorem sol0 : rat.toLP.basicSol {0} = ![1/2, 0] := by
  symm; apply (basis 0).eq_basicSol
  · ext i; fin_cases i; norm_num [rat, RatLP.toLP, mulVec, dotProduct, Fin.sum_univ_succ]
  · intro j hj; fin_cases j <;> simp_all

private theorem sol1 : rat.toLP.basicSol {1} = ![0, 1/2] := by
  symm; apply (basis 1).eq_basicSol
  · ext i; fin_cases i; norm_num [rat, RatLP.toLP, mulVec, dotProduct, Fin.sum_univ_succ]
  · intro j hj; fin_cases j <;> simp_all

private theorem feasible (j : Fin 2) : rat.toLP.IsFeasibleBasis {j} := by
  refine ⟨basis j, ?_⟩
  fin_cases j
  · change ∀ k, 0 ≤ rat.toLP.basicSol {0} k
    rw [sol0]; intro k; fin_cases k <;> norm_num
  · change ∀ k, 0 ≤ rat.toLP.basicSol {1} k
    rw [sol1]; intro k; fin_cases k <;> norm_num

private theorem nd (j : Fin 2) : rat.toLP.IsNondegenerate {j} := by
  intro k hk
  have he : k = j := mem_singleton.mp hk
  subst k
  fin_cases j <;> simp [sol0, sol1]

private theorem dir : rat.toLP.basicDir {1} 0 = ![1, -1] := by
  symm; apply (basis 1).eq_basicDir (by decide)
  refine ⟨?_, by norm_num, ?_⟩
  · ext i; fin_cases i; norm_num [rat, RatLP.toLP, mulVec, dotProduct, Fin.sum_univ_succ]
  · intro j hj hne; fin_cases j <;> simp_all

private theorem improving : rat.toLP.improving {1} = {0} := by
  have hr := (basis 1).cost_basicDir (j := 0) (by decide)
  rw [dir] at hr
  have hc : rat.toLP.c ⬝ᵥ ![1, -1] = -(1/3 : ℝ) := by
    norm_num [rat, RatLP.toLP, dotProduct, Fin.sum_univ_succ]
  have hr0 : rat.toLP.reducedCost {1} 0 = -(1/3 : ℝ) := hr.symm.trans hc
  ext j
  fin_cases j
  · simp only [LP.improving, mem_filter, mem_univ, true_and]
    change (rat.toLP.reducedCost {1} (0 : Fin 2) < 0) ↔ (0 : Fin 2) ∈ {0}
    rw [hr0]
    norm_num
  · simp only [LP.improving, mem_filter, mem_univ, true_and]
    change (rat.toLP.reducedCost {1} (1 : Fin 2) < 0) ↔ (1 : Fin 2) ∈ {0}
    rw [show rat.toLP.reducedCost {1} 1 = 0 from (basis 1).reducedCost_of_mem (by decide)]
    norm_num

private theorem optimal : rat.toLP.IsOptimalBasis {0} := by
  refine ⟨feasible 0, ⟨(basis 0).basicSol_spec.1, (feasible 0).2⟩, ?_⟩
  intro y hy
  have he := congrFun hy.1 0
  have hp := hy.2 1
  rw [sol0]
  norm_num [rat, RatLP.toLP, mulVec, dotProduct, Fin.sum_univ_succ] at he ⊢
  linarith

private def trace (k : ℕ) : Finset (Fin 2) := if k = 0 then {1} else {0}

private theorem run : rat.toLP.IsSimplexRunWith rat.toLP.IsDantzigChoice 1 trace := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro k _; by_cases hk : k = 0 <;> simp only [trace, hk, ite_true, ite_false]
    · exact feasible 1
    · exact feasible 0
  · intro k hk
    have : k = 0 := by omega
    subst k
    simp only [trace, ite_true, Nat.reduceAdd, one_ne_zero, ite_false]
    have himp : (0 : Fin 2) ∈ rat.toLP.improving {1} := by rw [improving]; simp
    refine ⟨0, ⟨himp, ?_⟩, feasible 1, himp, by decide, 1, ?_, by decide⟩
    · intro j hj; rw [improving, mem_singleton] at hj; subst j; rfl
    · refine ⟨by decide, ?_, ?_⟩
      · rw [dir]; norm_num
      · intro j hj _; have he := mem_singleton.mp hj; subst j; rfl
  · simpa only [trace, one_ne_zero, ite_false] using
      (LP.optimal_iff (feasible 0) (nd 0)).1 optimal

private theorem unique : ∀ k < 1, ∀ j j', rat.toLP.IsDantzigChoice (trace k) j →
    rat.toLP.IsDantzigChoice (trace k) j' → j = j' := by
  intro k hk j j' hj hj'
  have : k = 0 := by omega
  subst k
  have hj0 : j = 0 := by simpa only [trace, ite_true, improving, mem_singleton] using hj.1
  have hj'0 : j' = 0 := by simpa only [trace, ite_true, improving, mem_singleton] using hj'.1
  exact hj0.trans hj'0.symm

example : IsWolfeRunWith rat.integerize.cap.atom (IsLinoptChoice rat.integerize.cap.atom)
    1 (fun k ↦ hat (hat (trace k))) :=
  (rat.integer_count_transfer 1 trace run (by
    intro k _; by_cases hk : k = 0 <;> simp only [trace, hk, ite_true, ite_false]
    · exact nd 1
    · exact nd 0) unique).1

example : (Construction.Cap.run rat.integerize).value = rat.integerize.cap :=
  Construction.Cap.run_correct _

private def input : QueryInput 1 2 where
  lp := rat
  initial := fun _ ↦ 1
  feasible := by simpa [basisOf] using feasible 1
  owner := fun _ ↦ 0
  positive := by intro i; fin_cases i; norm_num [rat, RatLP.toLP]
  offOwner := by intro i j h; exact (h (Subsingleton.elim _ _)).elim
  terminates := ⟨1, trace, run, by simp [trace, basisOf]⟩

private def query : QueryInstance := ⟨1, 2, input, 0⟩
private def queryOld : QueryInstance := ⟨1, 2, input, 1⟩

private theorem source_ever : query.sourceCorrect .ever True := by
  change ∀ f (B : ℕ → Finset (Fin 2)),
    rat.toLP.IsSimplexRunWith rat.toLP.IsDantzigChoice f B →
    B 0 = basisOf (fun _ : Fin 1 ↦ (1 : Fin 2)) →
    (sourceEvent .ever rat.toLP f B 0 ↔ True)
  intro f B hB h0
  have hstart : B 0 = {1} := h0.trans (by decide)
  have hf : 0 < f := by
    by_contra hn
    have he : f = 0 := by omega
    have ht := hB.2
    rw [he, hstart, improving] at ht
    simp at ht
  obtain ⟨j, hj, hp⟩ := hB.1.2 0 hf
  have he : j = 0 := by
    have hi := hj.1
    change j ∈ rat.toLP.improving (B 0) at hi
    rw [hstart, improving, mem_singleton] at hi
    exact hi
  change (∃ k < f, rat.toLP.IsPivot (B k) 0 (B (k + 1))) ↔ True
  exact iff_true_intro ⟨0, hf, he ▸ hp⟩

private theorem terminal_basis (f : ℕ) (B : ℕ → Finset (Fin 2))
    (hB : rat.toLP.IsSimplexRunWith rat.toLP.IsDantzigChoice f B) : B f = {0} := by
  have hcard : (B f).card = 1 := (hB.1.1 f le_rfl).1.1
  have hzero : (0 : Fin 2) ∈ B f := by
    by_contra hn
    have hs : B f ⊆ {1} := by
      intro j hj
      fin_cases j
      · exact (hn (by simpa using hj)).elim
      · simp
    have he : B f = {1} := Finset.eq_of_subset_of_card_le hs (by simpa using hcard.ge)
    have ht := hB.2
    rw [he, improving] at ht
    simp at ht
  exact (Finset.card_eq_one.mp hcard).elim (fun j hj ↦ by
    rw [hj, mem_singleton] at hzero
    simpa only [hzero] using hj)

private theorem source_final : query.sourceCorrect .final True := by
  change ∀ f (B : ℕ → Finset (Fin 2)),
    rat.toLP.IsSimplexRunWith rat.toLP.IsDantzigChoice f B →
    B 0 = basisOf (fun _ : Fin 1 ↦ (1 : Fin 2)) → ((0 : Fin 2) ∈ B f ↔ True)
  intro f B hB _
  rw [terminal_basis f B hB]
  exact iff_true_intro (mem_singleton_self _)

example : query.targetQuestion .ever :=
  (query.answer_transfer .ever (by intro _; decide) True source_ever).2 trivial

example : query.targetQuestion .final :=
  (query.answer_transfer .final (by intro h; cases h) True source_final).2 trivial

/-- The final query also supports an initially basic label; it leaves here. -/
example : ¬ queryOld.targetQuestion .final := by
  have hs : queryOld.sourceCorrect .final False := by
    change ∀ f (B : ℕ → Finset (Fin 2)),
      rat.toLP.IsSimplexRunWith rat.toLP.IsDantzigChoice f B →
      B 0 = basisOf (fun _ : Fin 1 ↦ (1 : Fin 2)) → ((1 : Fin 2) ∈ B f ↔ False)
    intro f B hB _
    rw [terminal_basis f B hB]; simp
  exact (queryOld.answer_transfer .final (by intro h; cases h) False hs).1

end WolfeSimplex.Corollary4Check

run_cmd WolfeSimplex.Audit.project
