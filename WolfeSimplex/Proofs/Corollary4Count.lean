import WolfeSimplex.Proofs.NetworkIncidence
import WolfeSimplex.Proofs.RationalPreprocessBounds

/-! Exact counting transfer from rational network runs. Complexity-theoretic
hardness is not assumed in any of the conversion lemmas. -/

namespace WolfeSimplex
open Finset Wolfe

namespace RatLP
variable {m n : ℕ} (R : RatLP m n)

theorem integer_count_transfer (f : ℕ) (B : ℕ → Finset (Fin n))
    (hB : R.toLP.IsSimplexRunWith R.toLP.IsDantzigChoice f B)
    (hnd : ∀ k ≤ f, R.toLP.IsNondegenerate (B k))
    (hu : ∀ k < f, ∀ j j', R.toLP.IsDantzigChoice (B k) j →
      R.toLP.IsDantzigChoice (B k) j' → j = j') :
    IsWolfeRunWith R.integerize.cap.atom (IsLinoptChoice R.integerize.cap.atom) f
      (fun k ↦ hat (hat (B k))) ∧
    ∀ g S, IsWolfeRunWith R.integerize.cap.atom (IsLinoptChoice R.integerize.cap.atom) g S →
      S 0 = hat (hat (B 0)) → g = f ∧ ∀ k ≤ f, S k = hat (hat (B k)) := by
  have hI := (R.integerize_run f B).2 hB
  have hIn : ∀ k ≤ f, R.integerize.toLP.IsNondegenerate (B k) :=
    fun k hk ↦ (R.integerize_nondegenerate (B k)).2 (hnd k hk)
  have hopt : ∃ x, R.integerize.toLP.IsOptimalSolution x := by
    have ho := (LP.optimal_iff (hI.1.1 f le_rfl) (hIn f le_rfl)).2 hI.2
    exact ⟨R.integerize.toLP.basicSol (B f), ho.2⟩
  have hIu : ∀ k < f, ∀ j j', R.integerize.toLP.IsDantzigChoice (B k) j →
      R.integerize.toLP.IsDantzigChoice (B k) j' → j = j' := by
    intro k hk j j' hj hj'
    exact hu k hk j j' ((R.integerize_choice (B k) (hB.1.1 k hk.le) j).1 hj)
      ((R.integerize_choice (B k) (hB.1.1 k hk.le) j').1 hj')
  exact ⟨IntLP.capped_linopt_run_of_nondegenerate hopt f B hI hIn,
    fun g S hS h0 ↦ IntLP.capped_linopt_run_matches_of_unique hopt f B hI hIn hIu g S hS h0⟩

end RatLP

structure RationalNetwork (v n : ℕ) where
  tail : Fin n → Fin v
  head : Fin n → Fin v
  supply : Fin v → ℚ
  cost : Fin n → ℚ
  capacity : Fin n → ℚ

namespace RationalNetwork
variable {v n m c : ℕ} (Q : RationalNetwork v n)

def toNetwork : FlowNetwork v n where
  tail := Q.tail
  head := Q.head
  supply := fun w ↦ (Q.supply w : ℝ)
  cost := fun e ↦ (Q.cost e : ℝ)
  capacity := fun e ↦ (Q.capacity e : ℝ)

variable (D : Q.toNetwork.RowDeletion m c)

def standard : RatLP (m + n) (n + n) where
  A := fun r j ↦ Fin.addCases
    (fun i ↦ Fin.addCases
      (fun e ↦ (if Q.head e = (D.rows i).val then 1 else 0) -
        (if Q.tail e = (D.rows i).val then 1 else 0)) (fun _ ↦ 0) j)
    (fun e ↦ Fin.addCases (fun k ↦ if e = k then 1 else 0)
      (fun k ↦ if e = k then 1 else 0) j) r
  b := Fin.append (fun i ↦ Q.supply (D.rows i).val) Q.capacity
  c := Fin.append Q.cost 0

private theorem lp_ext {P Q : LP m n} (hA : P.A = Q.A) (hb : P.b = Q.b)
    (hc : P.c = Q.c) : P = Q := by
  cases P; cases Q; cases hA; cases hb; cases hc; rfl

theorem standard_toLP : (Q.standard D).toLP = D.bounded.standard := by
  apply lp_ext
  · funext r j
    refine Fin.addCases (fun i ↦ ?_) (fun e ↦ ?_) r <;>
      refine Fin.addCases (fun k ↦ ?_) (fun k ↦ ?_) j <;>
      simp [standard, RatLP.toLP, BoundedLP.standard, FlowNetwork.RowDeletion.bounded,
        FlowNetwork.incidence, toNetwork, -Fin.natAdd_eq_addNat] <;>
      split_ifs <;> simp_all
  · funext r
    refine Fin.addCases (fun i ↦ ?_) (fun e ↦ ?_) r <;>
      simp [standard, RatLP.toLP, BoundedLP.standard, FlowNetwork.RowDeletion.bounded,
        toNetwork, -Fin.natAdd_eq_addNat]
  · funext j
    refine Fin.addCases (fun k ↦ ?_) (fun k ↦ ?_) j <;>
      simp [standard, RatLP.toLP, BoundedLP.standard, FlowNetwork.RowDeletion.bounded,
        toNetwork, -Fin.natAdd_eq_addNat]

/-- The target is computed from the input and its initial forest, not its run
length. It has `2n+2` integer atoms in dimension `m+n+2`. -/
def target : IntLP (m + n + 1) (n + n + 1) := (Q.standard D).integerize.cap

theorem count_transfer (f : ℕ) (S : ℕ → BoundedLP.State n)
    (hb : D.Balanced) (hS : D.IsDantzigRun f S)
    (hp : ∀ e, 0 < (Q.capacity e : ℝ))
    (hnd : ∀ k ≤ f, ∀ e ∈ (S k).tree, 0 < (S k).flow e ∧
      (S k).flow e < (Q.capacity e : ℝ))
    (hu : ∀ k < f, ∀ j j', Q.toNetwork.IsDantzigChoice (S k) j →
      Q.toNetwork.IsDantzigChoice (S k) j' → j = j') :
    IsWolfeRunWith (Q.target D).atom (IsLinoptChoice (Q.target D).atom) f
      (fun k ↦ hat (hat (S k).basis)) ∧
    ∀ g T, IsWolfeRunWith (Q.target D).atom (IsLinoptChoice (Q.target D).atom) g T →
      T 0 = hat (hat (S 0).basis) → g = f ∧
        ∀ k ≤ f, T k = hat (hat (S k).basis) := by
  have hrun := D.standard_run f S hb hS
  have hs := D.run_to_bounded f S hb hS
  have hn : ∀ k ≤ f, D.bounded.standard.IsNondegenerate (S k).basis := by
    intro k hk
    exact BoundedLP.standard_nondegenerate _ _ (hs.1 k hk) hp (hnd k hk)
  have huniq : ∀ k < f, ∀ j j', D.bounded.standard.IsDantzigChoice (S k).basis j →
      D.bounded.standard.IsDantzigChoice (S k).basis j' → j = j' := by
    intro k hk
    apply BoundedLP.standard_unique _ _ (hs.1 k hk.le)
    intro j j' hj hj'
    exact hu k hk j j' ((D.dantzig_iff (S k) (hS.1 k hk.le) j).2 hj)
      ((D.dantzig_iff (S k) (hS.1 k hk.le) j').2 hj')
  have hr : (Q.standard D).toLP.IsSimplexRunWith (Q.standard D).toLP.IsDantzigChoice f
      (fun k ↦ (S k).basis) := by rwa [Q.standard_toLP D]
  have hn' : ∀ k ≤ f, (Q.standard D).toLP.IsNondegenerate (S k).basis := by
    rwa [Q.standard_toLP D]
  have hu' : ∀ k < f, ∀ j j', (Q.standard D).toLP.IsDantzigChoice (S k).basis j →
      (Q.standard D).toLP.IsDantzigChoice (S k).basis j' → j = j' := by
    rwa [Q.standard_toLP D]
  exact (Q.standard D).integer_count_transfer f (fun k ↦ (S k).basis) hr hn' hu'

end RationalNetwork
end WolfeSimplex
