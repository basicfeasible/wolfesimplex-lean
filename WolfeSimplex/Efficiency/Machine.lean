import WolfeSimplex.Execution.Machine
import WolfeSimplex.Efficiency.Corollary1

/-!
# Efficiency premises on executed programs

A complete Wolfe algorithm is one fixed first-order program, together with a
termination proof for each valid input. Outputs and cost fields below are derived
from its unique machine execution. The caller cannot assign a smaller body cost
or suppress a large intermediate integer in a report.
-/
namespace WolfeSimplex.Efficiency
open Execution

def targetData (i : Target) : List ℤ :=
  List.ofFn fun ij : Fin (i.N * i.D) ↦ i.points[ij.divNat][ij.modNat]

private def maskData {N : ℕ} (mask : Mask N) : List ℤ :=
  mask.toList.map fun b ↦ if b then 1 else 0

/-- The scratch frame is mutable. Points, the initial support and dimensions are
fixed input frames. Preparing these arrays and their cells is charged. -/
def machineInput (i : Target) : State where
  env := [[], targetData i, maskData i.initial, [i.N, i.D]]
  work := 4 * ((targetData i).length + i.N + 3)
  peak := Max.max (Code.magnitude (targetData i)) (Max.max 1 (Max.max i.N i.D))

/-- One finite program for all dimensions and coefficient values. The existence
of an efficient such program is a hypothesis of Corollary 1, not asserted here. -/
structure MachineAlgorithm where
  program : Program
  halts : ∀ i : Target, ∃ fuel result, Execution.execute program fuel (machineInput i) = some result

namespace MachineAlgorithm

noncomputable def fuel (A : MachineAlgorithm) (i : Target) : ℕ := (A.halts i).choose
noncomputable def result (A : MachineAlgorithm) (i : Target) : State :=
  (A.halts i).choose_spec.choose

theorem executed (A : MachineAlgorithm) (i : Target) :
    Execution.execute A.program (A.fuel i) (machineInput i) = some (A.result i) :=
  (A.halts i).choose_spec.choose_spec

/-- The chosen termination witness cannot affect the output or measured work. -/
theorem result_eq (A : MachineAlgorithm) (i : Target) (fuel : ℕ) (result : State)
    (h : Execution.execute A.program fuel (machineInput i) = some result) : A.result i = result :=
  Execution.execute_unique _ _ _ _ _ _ (A.executed i) h

/-- Emit one row of 0/1 support indicators per visited corral, including start
and finish. Reading and reversing that output is included in the public cost. -/
noncomputable def procedure (A : MachineAlgorithm) : WolfeProcedure := fun i ↦
  { trace := (A.result i).output.reverse.map fun row ↦
      Vector.ofFn fun j : Fin i.N ↦ decide (row[j.val]?.getD 0 ≠ 0)
    bodyWork := (A.result i).work
    numberBits := 1 + Nat.size (A.result i).peak }

/-- Corollary 1 restricted to machine executions, so the efficiency hypotheses
bound executed work and observed numbers instead of freely supplied metrics. -/
theorem report_transfer (A : MachineAlgorithm) :
    (PolynomialWolfe A.procedure → PolynomialSimplex (induce A.procedure)) ∧
    (StronglyPolynomialWolfe A.procedure → StronglyPolynomialSimplex (induce A.procedure)) :=
  Efficiency.corollary1 A.procedure

end MachineAlgorithm
end WolfeSimplex.Efficiency
