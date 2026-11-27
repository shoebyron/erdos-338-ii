module

/-
AUDITOR'S SUBSTITUTE for upstream `FormalConjecturesUtil.lean`
(google-deepmind/formal-conjectures @ ea8e3e198ded6fc73efb7f5653b74b28ac4ae1a8).

The upstream root module imports all of `FormalConjecturesForMathlib` and the
project linters, which are pinned to Lean v4.33.1. This substitute keeps only
what `FormalConjectures/ErdosProblems/338.lean` actually uses:

* `Mathlib`
* the unmodified upstream attribute implementation (`category`, `AMS`, `formal_proof`)
* the unmodified upstream `Set.lowerDensity` file

so that the unmodified upstream `338.lean` can be elaborated on Lean v4.35.0-rc3.
Linters are omitted; they do not change any definition or statement.
-/

public import Mathlib
public import FormalConjecturesForMathlib.Data.Set.Density
public import FormalConjecturesUtil.Attributes.Basic
