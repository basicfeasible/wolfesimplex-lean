import WolfeSimplex

/-! Small independent examples exercise the interpreter's array layout, signed
determinants, both preparation paths and a data-dependent machine loop. The
universal correctness/resource theorems are proved in the imported library. -/
open WolfeSimplex WolfeSimplex.Execution

private def matrix2 : Matrix (Fin 2) (Fin 2) ℤ := !![1, 2; 3, 4]
#guard (determinant 2).eval [pack matrix2] = [-2]

private def sample : IntLP 1 2 where
  A := !![1, 1]
  b := ![1]
  c := ![0, 1]
private def basis : Fin 1 → Fin 2 := fun _ ↦ 0

#guard (atomCode 1 2).eval (lpInput sample) = pack (integerAtoms sample)
#guard (shieldCode basis).eval (lpInput sample) =
  pack (integerAtoms (sample.shieldLP basis))
#guard (weightedCode basis (Equiv.refl _)).eval (lpInput sample) =
  pack (integerAtoms (sample.weightedLP basis (Equiv.refl _)))

private def countdown : Program := #[
  .constant 0 3, .constant 1 1, .emit 0,
  .arithmetic .sub 0 0 1, .positive 0 2 5, .halt]
private def initial : State := { env := [[]] }
#guard (Execution.execute countdown 20 initial).map (·.output.reverse) =
  some [[3, 1], [2, 1], [1, 1]]
#guard Execution.execute countdown 2 initial |>.isNone


private def memoryProgram : Program := #[
  .constant 0 7, .constant 1 42, .store 0 1, .load 0 0 2,
  .division false 3 2 0, .halt]
#guard (Execution.execute memoryProgram 10 initial).map (fun s ↦ Code.current s.env) =
  some [7, 42, 42, 6, 0, 0, 0, 42]
#guard (Execution.execute memoryProgram 10 initial).map (·.peak) = some 42

#eval IO.println "Primitive execution examples passed: determinant, atoms, both starts, loop, memory, division."
