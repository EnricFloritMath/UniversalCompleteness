import AsymptoticallyIntegerHD
import Lean.Util.CollectAxioms

/-!
# Project-axiom audit

This environment-wide check rejects every imported axiom whose originating
module belongs to the `AsymptoticallyIntegerHD` library, including private
declarations.
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let mut rejected : Array Name := #[]
  for (name, info) in env.constants.toList do
    if info.isAxiom then
      if let some moduleIdx := env.getModuleIdxFor? name then
        let moduleName := env.header.moduleNames[moduleIdx]!
        if (`AsymptoticallyIntegerHD).isPrefixOf moduleName then
          rejected := rejected.push name
  unless rejected.isEmpty do
    throwError "project-owned axiom declarations: {rejected.qsort Name.quickLt}"
