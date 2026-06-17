# comparator workspace

A minimal Lake workspace for running the real
[`leanprover/comparator`](https://github.com/leanprover/comparator) against this repo —
the external, independent re-verification driven by [`../verify.sh`](../verify.sh).

- `Challenge.lean` — the verbatim challenge spec (the *statements* comparator matches against).
- `Solution.lean` — bridge: re-states the headlines in `namespace JacobiansTest`, delegating
  to the proved declarations in `Jacobians.Challenge`.
- `config.json` — default run: the Riemann–Roch headline (`JacobiansTest.riemannRochL3`).
- `config-buzzard.json` — the 11 Buzzard property-theorem headlines.
- `lakefile.toml` — requires the parent repo as the `Jacobians` package (`path = "../.."`).
- `lean-toolchain` — pins `v4.30.0` (comparator + lean4export must match this).

Run from the repo root:

```bash
scripts/verify.sh                      # RR headline
scripts/verify.sh config-buzzard.json  # the 11 Buzzard headlines
```

`comparator` re-exports every proof via `lean4export` and re-checks it in a fresh kernel,
so the library `.olean`s are not trusted. A local **"Your solution is okay!"** mirrors a
green lean-eval run for `jacobian_challenge_diffgeo` (same toolchain, same Mathlib via the
parent repo, verbatim spec). `permitted_axioms` is the standard 3.
