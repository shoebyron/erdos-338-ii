import AuditAxioms

/-!
# Audit file 4 (written by the auditor; not part of the candidate ZIP)

Which locally built modules does the proof of `Erdos338.Bridge.boundedByOrder`
actually depend on?  Counts the reachable constants per defining module.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let root := ``Erdos338.Bridge.boundedByOrder
  let ((), acc) := (Audit.visit env root).run {}
  let mut counts : Std.HashMap Name Nat := {}
  let mut total : Nat := 0
  for n in acc.seen.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[idx.toNat]!
    let top := m.getRoot
    let key := if top == `Mathlib || top == `Init || top == `Std || top == `Lean
      || top == `Batteries || top == `Aesop || top == `Qq || top == `Plausible then top else m
    counts := counts.insert key (counts.getD key 0 + 1)
    total := total + 1
  let rows := counts.toArray.qsort (fun a b => a.1.toString < b.1.toString)
  logInfo m!"[audit] reachable constants by defining module (total {total}):"
  for (m, c) in rows do
    logInfo m!"[audit]   {m}: {c}"
  -- Conditional side-results must not be in the closure.
  for n in [``Erdos338.Bridge.AsymptoticKneser, `Erdos338.Bridge.boundedByOrder_of_asymptoticKneser,
      `Erdos338.Bridge.uniformDensityInput_of_hhp] do
    logInfo m!"[audit] closure mentions {n}: {acc.seen.contains n}"
