import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-! Executable audit helpers. These are checks on the Lean environment, not
additional axioms or mathematical hypotheses. -/

namespace WolfeSimplex.Audit

open Lean Elab Command

/-- Reject every axiom beyond Lean's standard classical foundation. -/
def check (decl : Name) : CommandElabM Unit := do
  let _ ← getConstInfo decl
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for axiomName in ← collectAxioms decl do
    unless allowed.contains axiomName do
      throwError "Unexpected axiom {axiomName} in {decl}"

/-- Check all declarations owned by imported project modules, including private
helpers and declarations not listed in the public theorem catalog. -/
def project : CommandElabM Unit := do
  let env ← getEnv
  let mut checked : Nat := 0
  for (decl, _) in env.constants do
    if let some index := env.getModuleIdxFor? decl then
      if env.header.moduleNames[index]!.toString.startsWith "WolfeSimplex." ||
          env.header.moduleNames[index]! == `WolfeSimplex then
        check decl
        checked := checked + 1
  unless checked > 0 do
    throwError "No project declarations found; import WolfeSimplex before auditing"
  logInfo m!"Axiom audit passed for all {checked} imported project declarations"

end WolfeSimplex.Audit
