import WolfeSimplex.Proofs.CapFacts

/-!
# Correspondence along a nondegenerate run

The counting argument in Appendix C.4 uses nondegeneracy only at the bases
visited by the source run. Other feasible bases may be degenerate. The cap
preserves runs from corresponding starts without a global nondegeneracy
assumption, and preserves nondegeneracy at each visited basis.

These results establish run and count transfers. They do not assert a
complexity-theoretic hardness result or assume one as a new axiom.
-/

namespace WolfeSimplex.IntLP

open Finset Wolfe

variable {m n : ℕ} {P : IntLP m n}

/-- A partial simplex run lifts when only its visited bases are nondegenerate.
The choice correspondence is needed only at those bases. -/
theorem partialRun_hat_of_nondegenerate (hm : 1 ≤ m)
    (wch : Finset (Fin (n + 1)) → Fin (n + 1) → Prop)
    (sch : Finset (Fin n) → Fin n → Prop)
    (f : ℕ) (B : ℕ → Finset (Fin n))
    (hB : P.toLP.IsPartialSimplexRunWith sch f B)
    (hnd : ∀ k ≤ f, P.toLP.IsNondegenerate (B k))
    (hch : ∀ k ≤ f, ∀ j : Fin n, wch (hat (B k)) j.castSucc ↔ sch (B k) j) :
    IsPartialWolfeRunWith P.atom wch f (fun k ↦ hat (B k)) := by
  refine ⟨fun k hk ↦ (thm_a_of_nondegenerate hm (hB.1 k hk) (hnd k hk)).1,
    fun k hk ↦ ?_⟩
  obtain ⟨j, hsj, hBk, hj, -, i, hi, heq⟩ := hB.2 k hk
  have hnd' : P.toLP.IsNondegenerate (insert j ((B k).erase i)) := by
    rw [← heq]
    exact hnd (k + 1) (by omega)
  refine ⟨j.castSucc, (hch k hk.le j).2 hsj, ?_⟩
  exact ((thm_b_of_nondegenerate hm hBk hj hi (hnd k hk.le) hnd').2.2.2.2 _).2
    (congrArg hat heq)

/-- Complete runs have exactly the same number of pivots and major cycles;
nondegeneracy is required only along the given source run. -/
theorem run_hat_of_nondegenerate (hm : 1 ≤ m)
    (wch : Finset (Fin (n + 1)) → Fin (n + 1) → Prop)
    (sch : Finset (Fin n) → Fin n → Prop)
    (f : ℕ) (B : ℕ → Finset (Fin n))
    (hB : P.toLP.IsSimplexRunWith sch f B)
    (hnd : ∀ k ≤ f, P.toLP.IsNondegenerate (B k))
    (hch : ∀ k ≤ f, ∀ j : Fin n, wch (hat (B k)) j.castSucc ↔ sch (B k) j) :
    IsWolfeRunWith P.atom wch f (fun k ↦ hat (B k)) := by
  refine ⟨partialRun_hat_of_nondegenerate hm wch sch f B hB.1 hnd hch, ?_⟩
  rw [improving_hat (hB.1.1 f le_rfl) hm, hB.2, Finset.map_empty]

/-- Linopt and Dantzig correspond along a given nondegenerate run. -/
theorem linopt_run_hat_of_nondegenerate (hm : 1 ≤ m)
    (f : ℕ) (B : ℕ → Finset (Fin n))
    (hB : P.toLP.IsSimplexRunWith P.toLP.IsDantzigChoice f B)
    (hnd : ∀ k ≤ f, P.toLP.IsNondegenerate (B k)) :
    IsWolfeRunWith P.atom (IsLinoptChoice P.atom) f (fun k ↦ hat (B k)) :=
  run_hat_of_nondegenerate hm _ _ f B hB hnd
    (fun k hk j ↦ linopt_hat_iff_of_nondegenerate hm (hB.1.1 k hk) (hnd k hk) j)

/-- If Dantzig has a unique choice along the given run, every partial linopt
run from its corresponding corral follows that run and cannot be longer.
No assumption is made about bases outside this particular run. -/
theorem linopt_partialRun_matches_of_unique (hm : 1 ≤ m)
    (f : ℕ) (B : ℕ → Finset (Fin n))
    (hB : P.toLP.IsSimplexRunWith P.toLP.IsDantzigChoice f B)
    (hnd : ∀ k ≤ f, P.toLP.IsNondegenerate (B k))
    (hunique : ∀ k < f, ∀ j j', P.toLP.IsDantzigChoice (B k) j →
      P.toLP.IsDantzigChoice (B k) j' → j = j')
    (g : ℕ) (S : ℕ → Finset (Fin (n + 1)))
    (hS : IsPartialWolfeRunWith P.atom (IsLinoptChoice P.atom) g S)
    (h0 : S 0 = hat (B 0)) :
    g ≤ f ∧ ∀ k ≤ g, S k = hat (B k) := by
  have key : ∀ k, k ≤ g → k ≤ f → S k = hat (B k) := by
    intro k
    induction k with
    | zero => intro _ _; exact h0
    | succ k ih =>
      intro hkg hkf
      have hSk := ih (by omega) (by omega)
      obtain ⟨j, hchoice, hBk, hj, -, i, hi, heq⟩ := hB.1.2 k (by omega)
      obtain ⟨j', hchoice', hmajor⟩ := hS.2 k (by omega)
      rw [hSk] at hchoice' hmajor
      have hj' := hmajor.2.1
      rw [improving_hat hBk hm, Finset.mem_map] at hj'
      obtain ⟨l, -, rfl⟩ := hj'
      have hl := (linopt_hat_iff_of_nondegenerate hm hBk (hnd k (by omega)) l).1 hchoice'
      have hlj : l = j := hunique k (by omega) l j hl hchoice
      subst l
      have hnd' : P.toLP.IsNondegenerate (insert j ((B k).erase i)) := by
        rw [← heq]
        exact hnd (k + 1) hkf
      have hnext := ((thm_b_of_nondegenerate hm hBk hj hi
        (hnd k (by omega)) hnd').2.2.2.2 _).1 hmajor
      exact hnext.trans (congrArg hat heq).symm
  have hgf : g ≤ f := by
    by_contra h
    have hfg : f < g := by omega
    obtain ⟨j, -, hmajor⟩ := hS.2 f hfg
    have hj := hmajor.2.1
    rw [key f hfg.le le_rfl, improving_hat (hB.1.1 f le_rfl) hm,
      hB.2, Finset.map_empty] at hj
    exact Finset.notMem_empty j hj
  exact ⟨hgf, fun k hk ↦ key k hk (hk.trans hgf)⟩

/-- Every complete linopt execution has exactly the source run's length and
the same successive supports, under uniqueness along that source run. -/
theorem linopt_run_matches_of_unique (hm : 1 ≤ m)
    (f : ℕ) (B : ℕ → Finset (Fin n))
    (hB : P.toLP.IsSimplexRunWith P.toLP.IsDantzigChoice f B)
    (hnd : ∀ k ≤ f, P.toLP.IsNondegenerate (B k))
    (hunique : ∀ k < f, ∀ j j', P.toLP.IsDantzigChoice (B k) j →
      P.toLP.IsDantzigChoice (B k) j' → j = j')
    (g : ℕ) (S : ℕ → Finset (Fin (n + 1)))
    (hS : IsWolfeRunWith P.atom (IsLinoptChoice P.atom) g S)
    (h0 : S 0 = hat (B 0)) :
    g = f ∧ ∀ k ≤ f, S k = hat (B k) := by
  obtain ⟨hgf, hsame⟩ := linopt_partialRun_matches_of_unique hm f B hB hnd hunique g S hS.1 h0
  have hfg : f ≤ g := by
    by_contra h
    have hgf' : g < f := by omega
    obtain ⟨j, -, -, hj, -⟩ := hB.1.2 g hgf'
    have hj' : j.castSucc ∈ improving P.atom (affineMin P.atom (S g)) := by
      rw [hsame g le_rfl, improving_hat (hB.1.1 g hgf) hm]
      exact Finset.mem_map_of_mem _ hj
    rw [hS.2] at hj'
    exact Finset.notMem_empty _ hj'
  have heq := le_antisymm hgf hfg
  exact ⟨heq, fun k hk ↦ hsame k (hk.trans hfg)⟩

/-- The cap preserves nondegeneracy at an individual feasible basis. -/
theorem isNondegenerate_hat_cap {B : Finset (Fin n)}
    (hB : P.toLP.IsFeasibleBasis B) (hnd : P.toLP.IsNondegenerate B) :
    P.cap.toLP.IsNondegenerate (hat B) := by
  intro j hj
  induction j using Fin.lastCases with
  | last => linarith [P.one_le_basicSol_hat_cap_last hB.1]
  | cast j =>
    rw [P.basicSol_hat_cap hB.1, capLift_castSucc]
    exact hnd j (by simpa using hj)

/-- Dantzig's choices are preserved by the cap, including all ties. -/
theorem dantzig_hat_cap_iff {B : Finset (Fin n)}
    (hB : P.toLP.IsFeasibleBasis B) (j : Fin n) :
    P.cap.toLP.IsDantzigChoice (hat B) j.castSucc ↔ P.toLP.IsDantzigChoice B j := by
  exact LP.dantzig_transfer P.toLP P.cap.toLP 1 (by norm_num)
    (fun _ hB ↦ P.improving_hat_cap hB.1)
    (fun _ hB j ↦ by simpa using P.reducedCost_hat_cap hB.1 j) B hB j

/-- Capping preserves every partial run from a corresponding start. No rank,
boundedness or global nondegeneracy hypothesis is needed. -/
theorem cap_partialRun_hat_iff (hopt : ∃ x, P.toLP.IsOptimalSolution x)
    (qch : Finset (Fin (n + 1)) → Fin (n + 1) → Prop)
    (pch : Finset (Fin n) → Fin n → Prop)
    (hch : ∀ B, P.toLP.IsFeasibleBasis B → ∀ j : Fin n,
      qch (hat B) j.castSucc ↔ pch B j)
    (B₀ : Finset (Fin n)) (hB₀ : P.toLP.IsFeasibleBasis B₀)
    (f : ℕ) (B' : ℕ → Finset (Fin (n + 1))) :
    (P.cap.toLP.IsPartialSimplexRunWith qch f B' ∧ B' 0 = hat B₀) ↔
      ∃ B, P.toLP.IsPartialSimplexRunWith pch f B ∧ B 0 = B₀ ∧
        ∀ k ≤ f, B' k = hat (B k) :=
  LP.transfer_partialRun_from_iff P.toLP P.cap.toLP
    (fun _ hB ↦ P.isFeasibleBasis_hat_cap hB)
    (fun _ hB ↦ P.improving_hat_cap hB.1)
    (fun _ hB _ hj i ↦ P.isLeavingLabel_hat_cap_iff hopt hB hj i)
    qch pch hch B₀ hB₀ f B'

/-- Capping also preserves the terminal condition and the exact run length. -/
theorem cap_run_hat_iff (hopt : ∃ x, P.toLP.IsOptimalSolution x)
    (qch : Finset (Fin (n + 1)) → Fin (n + 1) → Prop)
    (pch : Finset (Fin n) → Fin n → Prop)
    (hch : ∀ B, P.toLP.IsFeasibleBasis B → ∀ j : Fin n,
      qch (hat B) j.castSucc ↔ pch B j)
    (B₀ : Finset (Fin n)) (hB₀ : P.toLP.IsFeasibleBasis B₀)
    (f : ℕ) (B' : ℕ → Finset (Fin (n + 1))) :
    (P.cap.toLP.IsSimplexRunWith qch f B' ∧ B' 0 = hat B₀) ↔
      ∃ B, P.toLP.IsSimplexRunWith pch f B ∧ B 0 = B₀ ∧
        ∀ k ≤ f, B' k = hat (B k) :=
  LP.transfer_run_from_iff P.toLP P.cap.toLP
    (fun _ hB ↦ P.isFeasibleBasis_hat_cap hB)
    (fun _ hB ↦ P.improving_hat_cap hB.1)
    (fun _ hB _ hj i ↦ P.isLeavingLabel_hat_cap_iff hopt hB hj i)
    qch pch hch B₀ hB₀ f B'

/-- An integer LP with a finite optimum and a nondegenerate Dantzig run gives
a linopt run of the same length after capping, even if other feasible bases
are degenerate. The target has `n + 2` atoms in dimension `m + 2`. -/
theorem capped_linopt_run_of_nondegenerate (hopt : ∃ x, P.toLP.IsOptimalSolution x)
    (f : ℕ) (B : ℕ → Finset (Fin n))
    (hB : P.toLP.IsSimplexRunWith P.toLP.IsDantzigChoice f B)
    (hnd : ∀ k ≤ f, P.toLP.IsNondegenerate (B k)) :
    IsWolfeRunWith P.cap.atom (IsLinoptChoice P.cap.atom) f
      (fun k ↦ hat (hat (B k))) := by
  have hcap : P.cap.toLP.IsSimplexRunWith P.cap.toLP.IsDantzigChoice f
      (fun k ↦ hat (B k)) :=
    ((cap_run_hat_iff hopt _ _ (fun _ hB j ↦ dantzig_hat_cap_iff hB j)
      (B 0) (hB.1.1 0 (Nat.zero_le _)) f (fun k ↦ hat (B k))).2
      ⟨B, hB, rfl, fun _ _ ↦ rfl⟩).1
  exact linopt_run_hat_of_nondegenerate (by omega) f _ hcap
    (fun k hk ↦ isNondegenerate_hat_cap (hB.1.1 k hk) (hnd k hk))

/-- The cap preserves uniqueness of Dantzig's choice at a visited basis. -/
theorem dantzig_hat_cap_unique {B : Finset (Fin n)}
    (hB : P.toLP.IsFeasibleBasis B)
    (hunique : ∀ j j', P.toLP.IsDantzigChoice B j → P.toLP.IsDantzigChoice B j' → j = j') :
    ∀ j j', P.cap.toLP.IsDantzigChoice (hat B) j →
      P.cap.toLP.IsDantzigChoice (hat B) j' → j = j' := by
  intro j j' hj hj'
  have himp := hj.1
  have himp' := hj'.1
  rw [P.improving_hat_cap hB.1, Finset.mem_map] at himp himp'
  obtain ⟨i, -, rfl⟩ := himp
  obtain ⟨i', -, rfl⟩ := himp'
  exact congrArg Fin.castSucc (hunique i i' ((dantzig_hat_cap_iff hB i).1 hj)
    ((dantzig_hat_cap_iff hB i').1 hj'))

/-- All complete linopt runs after capping have the given source run's exact
length and supports. Only that source run must be nondegenerate and have unique
entering choices; unrelated feasible bases are unrestricted. -/
theorem capped_linopt_run_matches_of_unique (hopt : ∃ x, P.toLP.IsOptimalSolution x)
    (f : ℕ) (B : ℕ → Finset (Fin n))
    (hB : P.toLP.IsSimplexRunWith P.toLP.IsDantzigChoice f B)
    (hnd : ∀ k ≤ f, P.toLP.IsNondegenerate (B k))
    (hunique : ∀ k < f, ∀ j j', P.toLP.IsDantzigChoice (B k) j →
      P.toLP.IsDantzigChoice (B k) j' → j = j')
    (g : ℕ) (S : ℕ → Finset (Fin (n + 2)))
    (hS : IsWolfeRunWith P.cap.atom (IsLinoptChoice P.cap.atom) g S)
    (h0 : S 0 = hat (hat (B 0))) :
    g = f ∧ ∀ k ≤ f, S k = hat (hat (B k)) := by
  have hcap : P.cap.toLP.IsSimplexRunWith P.cap.toLP.IsDantzigChoice f
      (fun k ↦ hat (B k)) :=
    ((cap_run_hat_iff hopt _ _ (fun _ hB j ↦ dantzig_hat_cap_iff hB j)
      (B 0) (hB.1.1 0 (Nat.zero_le _)) f (fun k ↦ hat (B k))).2
      ⟨B, hB, rfl, fun _ _ ↦ rfl⟩).1
  exact linopt_run_matches_of_unique (by omega) f _ hcap
    (fun k hk ↦ isNondegenerate_hat_cap (hB.1.1 k hk) (hnd k hk))
    (fun k hk ↦ dantzig_hat_cap_unique (hB.1.1 k hk.le) (hunique k hk)) g S hS h0

end WolfeSimplex.IntLP
