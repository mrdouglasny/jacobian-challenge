# AGENTS.md — jacobian-challenge

Guidance for **all** coding agents (Codex, Claude Code, Cursor, Copilot, …) working
in this repo. This is a multi-agent community project (Kevin Buzzard's Jacobian
Challenge): collaborators' agents do most of the work under light human steering.
Apply these rules regardless of which agent you are.

## Read these first (authoritative)
- **`CLAUDE.md`** — the project rules. Despite the name, they apply to every agent:
  Lean pre-push verification, CI, **axiom soundness & vetting**, where major changes
  get discussed, the protected-files list, and gotchas.
- **`AXIOM_AUDIT.md`** — the axiom ledger + vetting protocol. When you add,
  remove, or strengthen an axiom, update the relevant **ledger entry** (the
  per-axiom row / vetting note) in the same commit. You do **not** need to update
  the numeric **axiom counts** (the header, `README.md` at-a-glance, or the
  by-class table) — the maintainer reconciles those at merge. CI prints the kernel
  count for reference but no longer fails on count drift.
- **`docs/planning/`** — per-workstream design docs (read the relevant one before
  large changes in that area).

## Non-negotiables
- **Axiom soundness.** `lake build` / `#print axioms` / CI check typechecking and
  sorry-freeness — **NOT axiom truth**. A false `axiom` passes CI. Before relying on
  any new **or strengthened** axiom, vet its statement for **satisfiability** (sketch
  a witness; for high-leverage axioms ask Gemini deep-think). See CLAUDE.md
  "Axiom soundness" + the worked false-axiom post-mortem (pinned issue #82).
- **Verify before push.** Validate any ≥20-LOC Lean change with `lake build <Module>`
  (or `lake build Jacobians`) before pushing. CI is final confirmation, not detection.
- **No `sorry` / no axioms to paper over a hard goal.** If you're stuck, report the
  blocker honestly; do not fake completion.
- **Major / soundness-touching changes need discussion first** (GitHub Discussion or
  a tracking issue), then a PR that links it. Routine discharges may go straight to PR.
- **Protected files are owner-vetted** (`.github/CODEOWNERS`). You may *propose* edits
  to `CLAUDE.md`, `AGENTS.md`, `.github/CODEOWNERS`, `.github/workflows/`, and the
  axiom-report/consistency scripts (`scripts/axiom_report.lean`,
  `scripts/check_axiom_consistency.sh`) via PR, but they do not merge without
  @mrdouglasny's review. **Do not attempt to weaken or bypass these guards** (the
  soundness scripts, the sorry/axiom CI gates, branch protection). `AXIOM_AUDIT.md`
  and `docs/axiom-report.txt` are *not* protected — the report is CI-regenerated and
  kernel-diffed, the audit is documentation — so routine discharge PRs update them
  directly.

## Provenance
Disclose AI-agent authorship in PRs (DCO sign-off / `Co-Authored-By`), and fill the
**Estimated human time** field in the PR template.
