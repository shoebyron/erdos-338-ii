# A uniform bound for the restricted order of an asymptotic basis

Lean proof and audit for the paper in [`paper/`](paper/Erdos338_paper.pdf).

## The result

A set A of nonnegative integers is an asymptotic basis of order at most h if every sufficiently large integer is a sum of at most h elements of A, with repetitions allowed. Its restricted order is the least t such that every sufficiently large integer is a sum of at most t *distinct* elements of A. The restricted order does not always exist.

Erdős and Graham asked whether the restricted order, when it exists, is bounded in terms of h alone. This is the boundedness question in [Erdős Problem 338](https://www.erdosproblems.com/338).

**Theorem.** There is a function f such that, for every A of order at most h with a finite restricted order, the restricted order of A is at most f(h).

The function f is given by a recursion and is very large. A lower bound of 2^(h−2) + h − 1 is known (Hegyvári, Hennecart and Plagne), so the true growth is at least exponential. The other two questions in Problem 338 are not treated here.

## Contents

| Folder | What it holds |
| --- | --- |
| `paper/` | The paper, as PDF and LaTeX source. |
| `lean/` | The Lean 4 project: nineteen modules, the pinned toolchain and manifest, and the build script `Verify.ps1`. |
| `audit/` | A separate audit: four audit files, the recorded logs, the scripts that produced them, and the upstream statement of the problem. |

`SHA256SUMS` lists every file in `lean/` and `audit/`. The files in both folders are unchanged from the audit archive. `audit/REDACTIONS.txt` describes the one redaction in that archive.

## Check the result

You need [elan](https://github.com/leanprover/elan) and a network connection. The project pins Lean 4.35.0-rc3. Its dependencies are pinned in `lean/lake-manifest.json`.

With PowerShell, from `lean/`:

```powershell
./Verify.ps1 -FetchCache
```

The script downloads the Mathlib cache, builds `FiniteModular`, and checks the other eighteen modules in dependency order. The last module, `Erdos338Unconditional.lean`, prints the axioms of the main theorem. The expected line is:

```
'Erdos338.Bridge.boundedByOrder' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The recorded run is `audit/logs/verify-original.log`. It took about 15 minutes with the cache.

## The formal statement

```lean
def HasOrder (A : Set ℕ) (h : ℕ) : Prop :=
  ∀ᶠ n in Filter.atTop, ∃ s : Multiset ℕ, (∀ x ∈ s, x ∈ A) ∧ s.card ≤ h ∧ s.sum = n

def HasRestrictedOrder (A : Set ℕ) (t : ℕ) : Prop :=
  ∀ᶠ n in Filter.atTop, ∃ s : Finset ℕ, (∀ x ∈ s, x ∈ A) ∧ s.card ≤ t ∧ s.sum id = n

theorem boundedByOrder :
    ∃ f : ℕ → ℕ, ∀ (A : Set ℕ) (h : ℕ), HasOrder A h →
      (∃ t, HasRestrictedOrder A t) → HasRestrictedOrder A (f h)
```

This is a readable summary. The definitions as Lean prints them are in `audit/logs/AuditAxioms.log`.

## What the audit records

| Check | Log in `audit/logs/` | Result |
| --- | --- | --- |
| Full build | `verify-original.log`, `verify-original.exit.txt` | Exit code 0. |
| Axioms of the main theorem and all it uses | `AuditAxioms.log` | Only `propext`, `Classical.choice`, `Quot.sound`. No unsafe or partial constant. |
| Same statement as the published conjecture | `AuditPublishedUpstream.log` | The type equals that of `erdos_338.variants.bounded_by_order` in [formal-conjectures](https://github.com/google-deepmind/formal-conjectures/blob/ea8e3e198ded6fc73efb7f5653b74b28ac4ae1a8/FormalConjectures/ErdosProblems/338.lean), up to bound-variable names. |
| Kernel check of an export | `leanchecker.from-export.log` | Accepted. |
| Kernel replay, module by module | `leanchecker.log`, `leanchecker.rerun-BoundedByOrderFixed.log` | 19 of 20 modules passed. `BoundedByOrderFixed` stopped on a file-read error and was replayed again separately; the rerun log shows no error and records no exit code. |
| External checker `lean4lean` | `lean4lean.replay.log`, `lean4lean.replay.exit.txt` | Did not run: it could not read the compiled files ("incompatible header"). It checked nothing. |

The scripts in `audit/tools/` contain the absolute Windows paths of the machine that ran them. Change those paths before you run them.

## Credits and licenses

- Kneser's addition theorem is used from [MiscYD](https://github.com/YaelDillies/misc-yd/tree/cd12c538d66f15a358a6904e7c847cd67661096f/MiscYD/AddCombi/Kneser), formalized by Mantas Bakšys and Yaël Dillies.
- `lean/SingleSetCovering.lean` adapts the files `Covering`, `Structure` and `Shift` from Daniel Veljjanoski's [erdos338-palomar](https://github.com/veljjanoski/erdos338-palomar/tree/a699263d0f7cdce0e5b3026bce86eab30973d0f8), under the Apache 2.0 license in `lean/LICENSE-SingleSetCovering.txt`.
- `audit/upstream/338.lean` is the statement file from [formal-conjectures](https://github.com/google-deepmind/formal-conjectures), under the Apache 2.0 license stated in its header.
- The proof builds on Chen, Yang and Zhao, [arXiv:2611.33191](https://arxiv.org/abs/2611.33191).
- Everything else is under the MIT license in [`LICENSE`](LICENSE).

## Use of AI tools

The mathematical content of the paper, namely Theorem 1.1 and its proof, and the Lean formalization, was generated by GPT-6.2 Astra (OpenAI).

## Citation

See [`CITATION.cff`](CITATION.cff).
