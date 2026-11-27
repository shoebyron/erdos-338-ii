import Erdos338Unconditional

/-!
# Audit file 1 (written by the auditor; not part of the candidate ZIP)

Type and axiom check of `Erdos338.Bridge.boundedByOrder`, run against the
`.olean` files produced by the unmodified `Verify.ps1`.
-/

open Lean

set_option pp.unicode.fun true

-- 1. The declaration, its kind, and its full type.
#check @Erdos338.Bridge.boundedByOrder
#print Erdos338.Bridge.boundedByOrder
#print Erdos338.Bridge.BoundedByOrder
#print Erdos338.Bridge.HasOrder
#print Erdos338.Bridge.HasRestrictedOrder
#print Erdos338.Bridge.Rep

-- 2. `BoundedByOrder` is definitionally the fully expanded statement (no hidden hypotheses).
example : Erdos338.Bridge.BoundedByOrder =
    (∃ f : ℕ → ℕ, ∀ (A : Set ℕ) (h : ℕ),
      (∀ᶠ n in Filter.atTop, ∃ s : Multiset ℕ, (∀ x ∈ s, x ∈ A) ∧ s.card ≤ h ∧ s.sum = n) →
      (∃ t : ℕ, ∀ᶠ n in Filter.atTop, ∃ s : Finset ℕ,
        (∀ x ∈ s, x ∈ A) ∧ s.card ≤ t ∧ ∑ x ∈ s, x = n) →
      ∀ᶠ n in Filter.atTop, ∃ s : Finset ℕ,
        (∀ x ∈ s, x ∈ A) ∧ s.card ≤ f h ∧ ∑ x ∈ s, x = n) := rfl

-- 3. Stock axiom report.
#print axioms Erdos338.Bridge.boundedByOrder
#print axioms Erdos338.Bridge.uniformDensityInput
#print axioms Erdos338.Bridge.uniformProgressionInput
#print axioms Erdos338.Bridge.boundedByOrder_of_analyticInputs
#print axioms Erdos338.FiniteModular.uniformModularBound

-- 4. Independent recomputation: walk every constant reachable from the theorem
--    (types, values, constructors, recursor rules) and list each axiom met.
namespace Audit

structure Acc where
  seen : NameSet := {}
  axioms : Array Name := #[]
  missing : Array Name := #[]
  theorems : Nat := 0
  unsafeOrPartial : Array Name := #[]

partial def visit (env : Environment) (n : Name) : StateM Acc Unit := do
  if (← get).seen.contains n then return
  modify fun a => { a with seen := a.seen.insert n }
  match env.find? n with
  | none => modify fun a => { a with missing := a.missing.push n }
  | some ci =>
    let deps (e : Expr) : StateM Acc Unit := e.getUsedConstants.forM (visit env)
    if ci.isUnsafe || ci.isPartial then
      modify fun a => { a with unsafeOrPartial := a.unsafeOrPartial.push n }
    deps ci.type
    match ci with
    | .axiomInfo _ => modify fun a => { a with axioms := a.axioms.push n }
    | .defnInfo v => deps v.value
    | .thmInfo v =>
      modify fun a => { a with theorems := a.theorems + 1 }
      deps v.value
    | .opaqueInfo v => deps v.value
    | .quotInfo _ => pure ()
    | .inductInfo v => v.ctors.forM (visit env)
    | .ctorInfo v => visit env v.induct
    | .recInfo v => v.rules.forM fun r => deps r.rhs

end Audit

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let root := ``Erdos338.Bridge.boundedByOrder
  let some ci := env.find? root | throwError "declaration not found"
  let kind := match ci with
    | .thmInfo _ => "theorem" | .axiomInfo _ => "AXIOM" | .defnInfo _ => "def"
    | .opaqueInfo _ => "OPAQUE" | _ => "other"
  let ((), acc) := (Audit.visit env root).run {}
  logInfo m!"[audit] kind = {kind}; universe params = {ci.levelParams}; \
    type = {ci.type}; type closed = {!ci.type.hasFVar && !ci.type.hasMVar && !ci.type.hasLooseBVars}"
  logInfo m!"[audit] constants reachable = {acc.seen.size}; theorems among them = {acc.theorems}"
  logInfo m!"[audit] axioms reachable = {acc.axioms.qsort Name.lt}"
  logInfo m!"[audit] constants missing from environment = {acc.missing}"
  logInfo m!"[audit] unsafe/partial constants reachable = {acc.unsafeOrPartial}"
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let extra := acc.axioms.filter (!allowed.contains ·)
  if extra.isEmpty && acc.missing.isEmpty then
    logInfo "[audit] PASS: only propext, Classical.choice, Quot.sound"
  else
    throwError "[audit] FAIL: unexpected axioms {extra} / missing {acc.missing}"
