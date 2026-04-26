# CLAUDE.md — jacobian-challenge

Project-specific guidance for Claude Code working on this repo.

## Pre-push Lean verification rule

The lean-lsp-mcp `lean_diagnostic_messages` tool is **unreliable** as a
"is this safe to push" check: it returns `success: false` with empty
`items` when files in the dependency graph aren't fully loaded. Empty
`items` looks like "no errors" but actually means "didn't finish
checking yet". This has caused multiple back-to-back CI failures.

**Rule.** Any commit that touches **≥20 LOC of real Lean** (not docs,
not pure renames, not formatting) MUST be validated before push by one
of:

1. **`lake env lean <file.lean>`** — compiles the file as the build
   would, ~5–30s for an incremental project file (Mathlib stays
   cached). **This is the most reliable check** and the one to use by
   default. Returns same errors/warnings as CI.

2. **`lean_run_code`** with a `#check` or `example` exercising the new
   declaration. Use as a quick sanity check during interactive
   development. **CAVEAT: can return false positives** — a snippet may
   compile when the imported file would fail (observed `b2ae9f9` →
   CI failure: `Decidable` instance error in the file did not surface
   in the snippet check). Always follow with `lake env lean` for
   pre-push validation.

3. **`lake build <ModulePath>`** for substantive proof work touching
   many files. Slower than `lake env lean` but checks downstream
   consumers too.

For tiny edits (docs, typo fixes, single-line renames), skip and rely
on CI as final confirmation.

**Sub-rule for `lean_run_code` tests.** The test snippet must exercise
the declaration **with the exact signature shape it actually has** —
same implicit/explicit/instance argument structure, same hypothesis
form. Specifically:

* Don't add `haveI`, `letI`, or extra hypotheses to the test's TYPE
  signature that aren't in the declaration's signature. Doing so
  elaborates the test in a richer context than the real def will see,
  hiding signature-time typeclass-synthesis failures.
* DO put `haveI` in the test's PROOF body when needed to discharge
  hypotheses for the call — that mirrors how downstream callers will
  use the declaration.
* For declarations that take `[TypeClass]` arguments, the test should
  let typeclass synthesis find them, not pass them explicitly.

Example failure mode that CI caught and `lean_run_code` missed
(EA3, commit `4c7a959` → fix `b7dd81a`): a def with body
`(H : ...) (h : ¬ Odd ...) := by haveI : Fact ... := ⟨h⟩; ...` and
return type `HolomorphicOneForm X` failed CI because the SIGNATURE
elaboration needed `ChartedSpace ℂ X` which only resolves under
`Fact`. The `haveI` in the body doesn't help signature elaboration.
Fix: take `[Fact ...]` as instance arg. The original test passed
because it added `haveI` in the test TYPE signature too — testing a
*corrected* version, not the actual def.

## CI

CI is GitHub Actions, runs `lake build` on every push to `main`. Each
run is ~4 min. Treat CI as **final confirmation**, not detection. Any
detected issue should be re-fixable from a clean local state in
seconds via `lean_run_code` or `lake build <Module>`.

## Branch structure

- `main` — current development with cross-pollination from
  `rkirov/jacobian-claude` (Apache 2.0). Default branch.
- `solo` — preserved snapshot of the repo before any outside
  contributions were imported (frozen at v0.2 of 2026-04-25).

When opening a PR, base against `main`.

## Vendored Kirov material

Verbatim copies live under `vendor/kirov-jacobian-claude/` (outside the
build root, not compiled). Modules ported into our build live under
`Jacobians/Vendor/Kirov/` with per-file Apache 2.0 attribution headers
and namespace renamed to `Jacobians.Vendor.Kirov.*`. Bridge files in
`Jacobians/Bridge/` connect our axiom layer to Kirov's real proofs.
See `docs/cross-repo-adoption.md` for the full module list and
adoption status.

## Common gotchas

- **Typeclass synthesis with explicit hypotheses.** When a type
  parameter takes a hypothesis like `(h : ¬ Odd ...)`, downstream
  typeclass synthesis can't recover it. The fix is to wrap as
  `[Fact (¬ Odd ...)]` so it's a typeclass argument, then callers
  declare `haveI : Fact (¬ Odd ...) := ⟨h⟩` once. See
  `Jacobians/ProjectiveCurve/Hyperelliptic/EvenAtlas.lean` for the
  pattern.
- **Convert the WHOLE chain, not just the top.** When converting a
  hypothesis-using type to `[Fact ...]`, every instance the typeclass
  synthesis traverses must take `[Fact ...]` (not explicit `(h : ...)`).
  Partial conversion looks like it works (top-level `inferInstance`
  succeeds in toy tests) but downstream typeclass synthesis hits the
  unconverted lower instance, fails, and **times out** rather than
  failing fast — `(deterministic) timeout at typeclass, maximum number
  of heartbeats (20000) has been reached`. Concrete failure: my EA3
  fix `b7dd81a` converted ChartedSpace and IsManifold on
  `HyperellipticEvenProj` to `[Fact ...]` but left T2Space /
  CompactSpace / ConnectedSpace in `Even.lean` with explicit `(h : ...)`.
  Codex's `a9e93fc` finished the conversion. Lesson: when starting a
  Fact-conversion of one instance, audit the dependency graph
  (`grep '(h : ¬ Odd'` etc.) and convert all participants in the same
  commit.
- **`reverseData` definitional equality.** `HyperellipticAffineInfinity H`
  is definitionally `HyperellipticAffine (HyperellipticAffineInfinity.reverseData H h)`
  for `h : ¬ Odd H.f.natDegree`. The `change` tactic accepts this, so
  the entire `HyperellipticAffine` atlas transfers to
  `HyperellipticAffineInfinity` with `change ... infer_instance`.
