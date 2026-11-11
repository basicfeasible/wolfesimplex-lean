import WolfeSimplex

/-! Run with `lake env lean scripts/CheckAxioms.lean`.
Check every declaration owned by imported project modules, including private
helpers. Reject any axiom beyond `propext`, `Classical.choice` and `Quot.sound`.
For an individual result, use `#print axioms WolfeSimplex.<declaration>` in Lean. -/

run_cmd WolfeSimplex.Audit.project
