import WolfeSimplex

/-! Trace-projection fixture: build a one-pivot Klee–Minty
input, supply its two-frame trace, project the masks and read the entering
label. This fixture is for this input only. The universal correctness theorem
has the explicit `CorrectWolfe` premise; no fixture is used in its proof. -/

open WolfeSimplex WolfeSimplex.Efficiency

private def exampleInput : Source where
  m := 1
  n := 2
  lp := kleeMinty 1
  initial := #v[false, true]
  admissible := (km_admissible 1 (by decide)).1
  feasible := by
    convert (km_admissible 1 (by decide)).2 using 1; decide

private def exampleWolfe : WolfeProcedure := fun i ↦
  { trace := [i.initial, Vector.ofFn fun j ↦ decide (j.val = 0 ∨ j.val + 1 = i.N)]
    bodyWork := 3 * (i.N + 1)
    numberBits := 1 }

#guard ((execute exampleWolfe exampleInput).1.trace.map Vector.toList) ==
  [[false, true], [true, false]]
#guard (execute exampleWolfe exampleInput).2 == [some (0 : Fin 2)]
#guard nextLabel #v[false, true] #v[true, false] == some (0 : Fin 2)
