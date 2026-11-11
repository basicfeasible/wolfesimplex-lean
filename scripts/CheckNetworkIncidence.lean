import WolfeSimplex.Proofs.NetworkIncidence
import WolfeSimplex.AxiomAudit

/-! Concrete parallel-arc network: derive its LP basis from a cut certificate
and check full conservation, including the row that is deleted. -/

namespace WolfeSimplex.NetworkIncidenceCheck
open Finset Matrix FlowNetwork

private def net : FlowNetwork 2 2 where
  tail := fun _ ↦ 0
  head := fun _ ↦ 1
  supply := ![-2, 2]
  cost := ![0, -1]
  capacity := ![4, 1]

private def deletion : net.RowDeletion 1 1 where
  component := fun _ ↦ 0
  root := fun _ ↦ 0
  root_component := by intro k; exact Subsingleton.elim _ _
  arc_component := by intro e; rfl
  rows :=
    { toFun := fun _ ↦ ⟨1, by decide⟩
      invFun := fun _ ↦ 0
      left_inv := fun _ ↦ Subsingleton.elim _ _
      right_inv := by
        rintro ⟨w, hw⟩
        apply Subtype.ext
        change w ≠ (0 : Fin 2) at hw
        fin_cases w
        · exact (hw rfl).elim
        · rfl }

private def forest : deletion.ForestCertificate ({0} : Finset (Fin 2)) where
  card := by decide
  cut := fun _ ↦ {1}
  no_root := by
    intro e k
    change (0 : Fin 2) ∉ {1}
    decide
  separates := by
    intro e
    left
    constructor
    · change (1 : Fin 2) ∈ {1}
      decide
    · change (0 : Fin 2) ∉ {1}
      decide
  others := by
    intro e f hne
    apply False.elim
    apply hne
    apply Subtype.ext
    exact (mem_singleton.mp f.property).trans (mem_singleton.mp e.property).symm

private lemma balanced : deletion.Balanced := by
  intro k
  fin_cases k
  norm_num [RowDeletion.vertices, deletion, net, Fin.sum_univ_succ]

/-- Independence is derived from the cut; it is not supplied as a premise. -/
example : deletion.bounded.toLP.IsBasis ({0} : Finset (Fin 2)) :=
  deletion.forest_isBasis forest

private def state : BoundedLP.State 2 := ⟨{0}, ∅, ![2, 0]⟩

private lemma native_state : deletion.IsState state := by
  refine ⟨⟨forest⟩, by decide, ⟨?_, ?_⟩, ?_⟩
  · ext w
    fin_cases w <;>
      norm_num [state, net, incidence, mulVec, dotProduct, Fin.sum_univ_succ]
  · intro e
    fin_cases e <;> norm_num [state, net]
  · intro e he
    fin_cases e <;> simp_all [state]

example : deletion.bounded.IsState state := deletion.state_to_bounded state balanced native_state

example : net.IsFeasible ![2, 0] := native_state.2.2.1

example : net.IsFundamental ({0} : Finset (Fin 2)) 1 ![-1, 1] := by
  refine ⟨?_, by norm_num, ?_⟩
  · ext w
    fin_cases w <;> norm_num [net, incidence, mulVec, dotProduct, Fin.sum_univ_succ]
  · intro e he hne
    fin_cases e <;> simp_all

end WolfeSimplex.NetworkIncidenceCheck

run_cmd WolfeSimplex.Audit.project
