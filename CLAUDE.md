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

1. **`lean_run_code`** with a `#check` or `example` exercising the new
   declaration. For new `instance`s, write `example : InferredType :=
   inferInstance`. For new theorems, write `example : T := myThm _ _`.
   For new defs, exercise them at a use site. This is the default
   for fast iteration.

2. **`lake build <ModulePath>`** for substantive proof work. Mathlib is
   cached; incremental builds of one or two files are ~10–60s. Use
   when `lean_run_code` snippets get awkward or when changes touch
   typeclass resolution (which `lean_run_code` exercises only at the
   snippet's use site, not at every downstream resolution point).

For tiny edits (docs, typo fixes, single-line renames), skip and rely
on CI as final confirmation.

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
- **`reverseData` definitional equality.** `HyperellipticAffineInfinity H`
  is definitionally `HyperellipticAffine (HyperellipticAffineInfinity.reverseData H h)`
  for `h : ¬ Odd H.f.natDegree`. The `change` tactic accepts this, so
  the entire `HyperellipticAffine` atlas transfers to
  `HyperellipticAffineInfinity` with `change ... infer_instance`.
