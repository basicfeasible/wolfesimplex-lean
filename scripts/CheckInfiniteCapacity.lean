import WolfeSimplex.Proofs.Corollary4InfiniteCapacity
import WolfeSimplex.AxiomAudit

/-! An uncapacitated entering arc has a deliberately zero placeholder capacity.
The old finite model would stop at that zero bound. The native extended model
ignores it, takes a genuine unit pivot, and normalization preserves the count. -/
namespace WolfeSimplex.InfiniteCapacityCheck
open Finset Matrix FlowNetwork PaperCorollary4

private def network : ExtendedNetwork 2 2 where
  data :=
    { tail := fun _ ↦ 0
      head := fun _ ↦ 1
      supply := ![-1, 1]
      cost := ![0, 1]
      capacity := ![0, 5] }
  infinite := {0}

private def deletion := network.data.deleteLast

private theorem terminal : network.Terminal := by
  intro e _
  left
  intro a
  change (1 : Fin 2) ≠ 0
  decide

private def forest (k : Fin 2) : deletion.ForestCertificate {k} where
  card := by simp
  cut := fun _ ↦ {0}
  no_root := by intro e c; change (1 : Fin 2) ∉ {0}; decide
  separates := by
    intro e
    right
    constructor
    · change (1 : Fin 2) ∉ {0}; decide
    · change (0 : Fin 2) ∈ {0}; decide
  others := by
    intro e f h
    exact (h (Subtype.ext ((mem_singleton.mp f.property).trans
      (mem_singleton.mp e.property).symm))).elim

private def state (k : Fin 2) : BoundedLP.State 2 :=
  ⟨{k}, ∅, fun e ↦ if e = k then 1 else 0⟩

private theorem isState (k : Fin 2) : network.IsState deletion (state k) := by
  refine ⟨⟨forest k⟩, by simp [state], ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · ext w
    fin_cases w <;> fin_cases k <;>
      norm_num [state, network, RationalNetwork.toNetwork, incidence, mulVec, dotProduct,
        Fin.sum_univ_succ]
  · intro e; simp only [state]; split_ifs <;> norm_num
  · intro e he
    fin_cases e
    · simp [network] at he
    · fin_cases k <;> norm_num [network, state]
  · simp [state]
  · intro e he
    have hk : e ≠ k := by simpa [state] using he
    simp [state, hk]

private theorem nondegenerate (k : Fin 2) : network.IsNondegenerate (state k) := by
  intro e he
  have hk : e = k := by simpa [state] using he
  subst e
  refine ⟨by simp [state], ?_⟩
  fin_cases k <;> norm_num [network, state]

private theorem fundamental (k j : Fin 2) (h : j ≠ k) :
    network.data.toNetwork.fundamental {k} j = (fun e ↦ if e = j then 1 else -1) := by
  have hn : j ∉ ({k} : Finset (Fin 2)) := by simpa using h
  rw [deletion.fundamental_eq (forest k) j hn]
  symm
  apply (deletion.forest_isBasis (forest k)).eq_basicDir hn
  refine ⟨(deletion.full_null_iff _).2 ?_, by simp, ?_⟩
  · ext i; fin_cases i <;> fin_cases j <;>
      norm_num [network, RationalNetwork.toNetwork, incidence, mulVec, dotProduct,
        Fin.sum_univ_succ]
  · intro e he hne
    fin_cases e <;> fin_cases k <;> fin_cases j <;> simp_all

private theorem cycleCost (k j : Fin 2) (h : j ≠ k) :
    network.data.toNetwork.cycleCost {k} j = if j = 0 then -1 else 1 := by
  rw [FlowNetwork.cycleCost, fundamental k j h]
  fin_cases j <;> norm_num [network, RationalNetwork.toNetwork, dotProduct, Fin.sum_univ_succ]

private theorem improving (j : Fin 2) :
    network.data.toNetwork.IsImproving (state 1) j ↔ j = 0 := by
  fin_cases j
  · simp [FlowNetwork.IsImproving, state, BoundedLP.sign, cycleCost 1 0 (by decide)]
  · simp [FlowNetwork.IsImproving, state]

private theorem choice : network.data.toNetwork.IsDantzigChoice (state 1) 0 := by
  refine ⟨(improving 0).2 rfl, ?_⟩
  intro j hj
  rw [(improving j).1 hj]

private theorem direction : network.data.toNetwork.orientedDirection (state 1) 0 = ![1, -1] := by
  change BoundedLP.sign (state 1) 0 • network.data.toNetwork.fundamental {1} 0 = _
  rw [show BoundedLP.sign (state 1) 0 = 1 by simp [state, BoundedLP.sign], one_smul,
    fundamental 1 0 (by decide)]
  ext e; fin_cases e <;> norm_num

private theorem pivot : network.IsPivot (state 1) 0 (state 0) := by
  refine ⟨(improving 0).2 rfl, BoundedLP.lower 1, ⟨network.hasBound_lower _, ?_, ?_⟩, ?_, ?_⟩
  · rw [direction]; norm_num [BoundedLP.liftDir_lower]
  · intro l hl hn
    rw [direction] at hn ⊢
    revert hl hn
    refine Fin.addCases (fun e ↦ ?_) (fun e ↦ ?_) l
    · fin_cases e <;> norm_num [BoundedLP.liftDir, BoundedLP.lower, FlowNetwork.residual,
        state, Fin.append, Fin.addCases, -Fin.natAdd_eq_addNat]
    · fin_cases e <;> norm_num [ExtendedNetwork.HasBound, network, BoundedLP.liftDir,
        BoundedLP.lower, FlowNetwork.residual, state, Fin.append, Fin.addCases,
        RationalNetwork.toNetwork, -Fin.natAdd_eq_addNat]
  · decide
  · rw [direction]
    ext e; fin_cases e <;>
      norm_num [FlowNetwork.residual, BoundedLP.lower, BoundedLP.liftDir, state,
        Fin.append, Fin.addCases]

private def trace (k : ℕ) := if k = 0 then state 1 else state 0

private theorem run : network.IsDantzigRun deletion 1 trace := by
  refine ⟨?_, ?_, ?_⟩
  · intro k _; unfold trace; split_ifs <;> apply isState
  · intro k hk
    have he : k = 0 := by omega
    subst k
    exact ⟨0, by simpa [trace] using choice, by simpa [trace] using pivot⟩
  · intro j hj
    change network.data.toNetwork.IsImproving (state 0) j at hj
    fin_cases j
    · simpa [FlowNetwork.IsImproving, state] using hj
    · norm_num [FlowNetwork.IsImproving, state, BoundedLP.sign,
        cycleCost 0 1 (by decide)] at hj

private def source : ExtendedNetworkInput where
  vertices := 2
  arcs := 2
  rows := 1
  components := 1
  network := network
  deletion := deletion
  initial := state 1
  nonempty := by decide
  balanced := by
    intro k; fin_cases k
    norm_num [FlowNetwork.RowDeletion.vertices, deletion, RationalNetwork.deleteLast,
      network, RationalNetwork.toNetwork, Fin.sum_univ_succ]
  terminal := terminal
  capacity := by
    intro e he; fin_cases e
    · simp [network] at he
    · norm_num [network]
  execution := ⟨1, trace, run, rfl,
    fun k _ ↦ by unfold trace; split_ifs <;> apply nondegenerate,
    fun k hk j j' hj hj' ↦ by
      have he : k = 0 := by omega
      subst k
      exact ((improving j).1 hj.1).trans ((improving j').1 hj'.1).symm⟩

#guard network.bound = 3
#guard network.finite.capacity 0 = 3
#guard network.finite.capacity 1 = 5
#guard (Execution.InfiniteCapacity.code 2 2).eval
  (Execution.InfiniteCapacity.input network) = [3, 5, 1, 1]

example : (network.deletion deletion).IsDantzigRun 1 trace :=
  network.run_to_finite deletion terminal 1 trace run

example : source.normalize.IsTargetCount 1 :=
  (source.count_transfer 1 trace run rfl
    (fun k _ ↦ by unfold trace; split_ifs <;> apply nondegenerate)
    (fun k hk j j' hj hj' ↦ by
      have he : k = 0 := by omega
      subst k
      exact ((improving j).1 hj.1).trans ((improving j').1 hj'.1).symm)).1

example : ¬ network.data.toNetwork.IsLeavingBound (state 1).flow ![1, -1] (BoundedLP.lower 1) := by
  intro h
  have hh := h.2 (BoundedLP.upper 0) (by norm_num [BoundedLP.liftDir_upper])
  norm_num [FlowNetwork.residual, BoundedLP.lower, BoundedLP.upper, BoundedLP.liftDir,
    state, network, RationalNetwork.toNetwork, Fin.append, Fin.addCases,
    -Fin.natAdd_eq_addNat] at hh

private def fractional : ExtendedNetwork 2 2 :=
  { network with data :=
      { network.data with
        supply := ![-1/2, 1/2]
        capacity := ![-999, 3/7] } }

#guard (Execution.InfiniteCapacity.code 2 2).eval
  (Execution.InfiniteCapacity.input fractional) = [3, 3, 1, 7]
#guard 999 ≤ ((Execution.InfiniteCapacity.code 2 2).run
  (Execution.InfiniteCapacity.input fractional)).peak

private def loop : ExtendedNetwork 1 1 where
  data := ⟨fun _ ↦ 0, fun _ ↦ 0, fun _ ↦ 0, fun _ ↦ 0, fun _ ↦ 0⟩
  infinite := {0}

example : ¬ loop.Terminal := by
  intro h
  rcases h 0 (by decide) with h | h <;> exact h 0 rfl

example : loop.IsFeasible (fun _ ↦ 4) := by
  refine ⟨?_, by intro e; norm_num, ?_⟩
  · ext w; fin_cases w
    norm_num [loop, RationalNetwork.toNetwork, incidence, mulVec, dotProduct, Fin.sum_univ_succ]
  · intro e he; fin_cases e; simp [loop] at he

#guard loop.bound = 1

end WolfeSimplex.InfiniteCapacityCheck

run_cmd WolfeSimplex.Audit.project
