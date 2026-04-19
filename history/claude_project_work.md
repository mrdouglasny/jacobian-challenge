# Claude project work log — jacobian-challenge

## 2026-04-19 — scaffold

Repo created in response to Kevin Buzzard's Jacobian Challenge (https://gist.github.com/kbuzzard/778bc714030b3e974ab5f4038783d1a9, v0.2), posted to Lean Zulip `#Autoformalization > Jacobian challenge` 2026-04-19.

Initial layout mirrors `hille-yosida` house style: `Jacobians/` source dir, top-level `Jacobians.lean` import, `lakefile.toml`, `docs/`, `history/`, Apache 2.0 license. Blueprint deferred to end per house convention.

Files created:
- `Jacobians/Challenge.lean` — verbatim copy of Buzzard's v0.2 gist
- `Jacobians/Basic.lean` — empty scratch
- `Jacobians.lean` — imports Challenge
- `lakefile.toml` — Mathlib pinned to commit `8e3c989104daaa052921bf43de9eef0e1ac9fbf5`
- `lean-toolchain` — `v4.30.0-rc1` (matches the pinned Mathlib's toolchain)
- `README.md`, `LICENSE` (Apache 2.0), `.gitignore`
- `docs/challenge-summary.md` — challenge statement + Zulip discussion recap
- `docs/plan.md` — Phase A–E roadmap
- `docs/status.md` — sorry inventory (22 sorries: 8 data defs, 4 instance props, 10 theorems), 0 axioms

Not yet done: `lake update`, `lake build`, CI, git init, GitHub remote.
