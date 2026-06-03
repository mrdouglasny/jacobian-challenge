# Runbook: produce discharge plans for all axioms

Goal: generate a **dependency-ordered roadmap** for discharging every axiom in
`jacobian-challenge` (99 axioms across 28 files, scoped to the `Jacobians`
lean_lib). Output goes to `docs/axiom-discharge-roadmap.md`.

This is set up to run from a **fresh Claude Code session in this repo** (e.g.
your other account). It uses multi-agent orchestration, so you must opt in
(say "use a workflow" / "ultracode", or just tell the agent to run the
Workflow file below).

## What it does

A 2-phase `Workflow`:

1. **Plan** — ~28 read-only `Explore` agents, one per file. Each enumerates the
   file's axioms, reads their docstrings + the `AXIOM_AUDIT.md` rows, greps
   `~/Documents/GitHub/catalogs/ALL_LEMMAS.tsv`, checks Mathlib (leansearch /
   loogle / local search), and emits a structured plan per axiom:
   `{ name, statement, why_axiomatized, route, findings, prereqs, blocked_by,
   effort, references }`.

   `route ∈ { mathlib-now, provable-from-other-axioms, needs-infra,
   genuine-textbook, spurious }`.

2. **Synthesize** — one agent folds all plans into a roadmap: counts by route,
   a "discharge now (cheap wins)" checklist, bounded-infrastructure groups, the
   genuine deep gaps in **dependency order** (topological over `blocked_by`),
   and a full per-axiom table.

It is **read-only** (Explore agents); it makes no edits to the project. The
only write is you saving the returned `roadmap` to disk afterward.

## How to run

From a Claude Code session in this repo, instruct the agent:

> Run the workflow in `scripts/axiom_discharge_plan.workflow.js`, then write the
> returned `roadmap` to `docs/axiom-discharge-roadmap.md`.

The agent should:

```
// 1. launch (opt-in required — this spawns ~30 agents)
Workflow({ scriptPath: "scripts/axiom_discharge_plan.workflow.js" })
// 2. when it returns { roadmap, real_count, files_done, plans }:
//    Write docs/axiom-discharge-roadmap.md  <- roadmap
//    (optionally also dump `plans` to docs/axiom-discharge-plans.json)
```

The workflow **returns** the markdown; the sandbox can't write files, so the
saving step is done by the launching agent after it returns.

## Cost / scale

~28 plan agents (queued ~10–16 concurrent) + 1 synthesis agent. Plan agents do
real per-axiom math triage + search, so this is a non-trivial token spend — it
was deliberately chosen over 99 single-axiom agents (one per file batches that
file's axioms). Inherits the session model for the plan agents (use Opus for
classification quality; downgrade to Sonnet in the script if you want to save
tokens — set `model: 'sonnet'` on the plan `agent()` call).

## Regenerating the file list

The `FILES` array in the workflow script came from `lean-fleet`:

```bash
cd ~/Documents/GitHub/lean-fleet && python3 - <<'PY'
import scan_fleet as sf, json, collections
from pathlib import Path
repo = Path("/Users/mdouglas/Documents/GitHub/jacobian-challenge")
rows=[r for r in sf.scan_repo("jacobian-challenge",repo) if r["kind"]=="axiom"]
print(json.dumps(sorted({r["path"] for r in rows})))
PY
```

(`lean-fleet` is the private orchestration repo: `mrdouglasny/lean-fleet`.)

## Notes
- The scanner has a minor false-positive (a wrapped signature word read as an
  axiom name); plan agents mark such entries `route: "spurious"` and the
  synthesis drops them.
- This produces *plans*, not proofs. Discharging the `mathlib-now` /
  `provable-from-other-axioms` items is the natural cheap first wave; the
  `genuine-textbook` gaps (Riemann–Roch, Serre duality, sheaf cohomology, …)
  are real multi-month projects and should stay axioms with vetted docstrings
  until that infrastructure exists.
