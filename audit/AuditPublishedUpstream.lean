import FormalConjectures.ErdosProblems.«338»
import Erdos338Unconditional

/-!
# Audit file 3 (written by the auditor; not part of the candidate ZIP)

Here `Erdos338.HasOrder` and `Erdos338.HasRestrictedOrder` are the constants
defined by the *unmodified* upstream file
`FormalConjectures/ErdosProblems/338.lean`
(google-deepmind/formal-conjectures @ ea8e3e198ded6fc73efb7f5653b74b28ac4ae1a8),
elaborated on the candidate's toolchain.

The statement below is typed out again rather than obtained from the upstream
theorem, and it is proved by the candidate theorem alone. The upstream
`sorry`-ed conjecture is never used in a proof; the final command only reads
its *type* to confirm that the two statements are the same expression.
-/

open Lean

set_option pp.unicode.fun true

namespace Erdos338Audit

theorem bounded_by_order :
    ∃ f : ℕ → ℕ, ∀ (A : Set ℕ) (h : ℕ), Erdos338.HasOrder A h →
      (∃ t, Erdos338.HasRestrictedOrder A t) → Erdos338.HasRestrictedOrder A (f h) :=
  Erdos338.Bridge.boundedByOrder

end Erdos338Audit

#print Erdos338.HasOrder
#print Erdos338.HasRestrictedOrder
#check @Erdos338Audit.bounded_by_order
#print axioms Erdos338Audit.bounded_by_order

-- For contrast: the upstream conjecture itself is `sorry`-ed.
#print axioms Erdos338.erdos_338.variants.bounded_by_order

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some up := env.find? ``Erdos338.erdos_338.variants.bounded_by_order
    | throwError "upstream constant not found"
  let some au := env.find? ``Erdos338Audit.bounded_by_order
    | throwError "audit constant not found"
  logInfo m!"[audit] upstream statement: {up.type}"
  logInfo m!"[audit] audit statement:    {au.type}"
  unless up.levelParams == au.levelParams do throwError "[audit] FAIL: universe parameters differ"
  if up.type == au.type then
    logInfo "[audit] PASS: audit statement and upstream `erdos_338.variants.bounded_by_order` \
      have identical types (Expr equality up to bound-variable names)"
  else
    throwError "[audit] FAIL: types differ"
  -- the audit proof term must not mention the upstream conjecture
  let some v := au.value? (allowOpaque := true) | throwError "[audit] audit theorem has no value"
  if v.getUsedConstants.contains ``Erdos338.erdos_338.variants.bounded_by_order then
    throwError "[audit] FAIL: audit proof uses the upstream conjecture"
  logInfo m!"[audit] audit proof term: {v}"
