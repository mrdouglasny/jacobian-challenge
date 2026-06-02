# Report: tangentstorm/JacobianChallenge methodology

*Authored 2026-06-02 from a read of the sibling repo
`github.com/tangentstorm/JacobianChallenge` (Michal Wallace). A parallel,
independent formalization of Buzzard's Jacobian Challenge — far larger than ours
(510 vs 84 Lean files, 2421 vs 428 lemmas, **0 axioms** vs our 102) and developed
as a documented, multi-model, agent-orchestrated operation. This is the most
mature working instance of the agent-driven model our own
[`centauro.md`](centauro.md) only designs, so it is worth studying closely.*

Primary sources read: `ref/methodology.md`, `ref/PROMPT.md`, the `scripts/`
toolchain, the `.github/workflows/`, the PR history, and the commit cadence.

## 1. Shape of the operation

- **One human (Michal Wallace) orchestrating a fleet of AI agents.** All 30
  recent PRs are his; the work is done by agents and integrated via PRs. Commit
  messages are tagged `[codex]`, `[MERGE]`, `Worker jc0…jc4`.
- **Cadence is the headline:** ~50–94 commits/day (94 on 2026-05-28, 90 on
  06-01); multiple PRs merged per day. "PR cadence becomes the project's
  heartbeat."
- **0-axiom discipline.** The project never uses the `axiom` keyword. The
  `Challenge.lean` public API is a **frozen set of 24 `sorry`s**; every gap is an
  honest `sorry` to be discharged bottom-up — the opposite of our axiom-staging.
- **Pinned toolchain**, recently bumped to Lean/Mathlib **v4.31.0-rc1** (ahead of
  our v4.30.0).

## 2. The methodology — three phases (`ref/methodology.md`)

A deliberate **"flesh out the proof, *then* formalize"** pipeline, run on the
**blueprint** as the spine:

- **Phase A — drive blueprint granularity down.** Apply a top-down refinement
  (`ref/TOPDOWN.md`) to the *informal* LaTeX proofs in `tex/`: promote every
  non-trivial proof step to its own `\begin{theorem/lemma/definition}` with
  `\label`/`\uses`/`\lean`, recursing until **every leaf is either already in
  Mathlib (`\notready`, no node) or a clean stand-alone "missing-from-Mathlib"
  statement (a node).** Gating signal: *no node hides a multi-thousand-line
  classical theorem.* The dep graph becomes a true Mathlib-gap inventory.
- **Phase B — per-leaf strategy elicitation, cross-model.** Before formalizing a
  gap, *plan* it: paste the leaf statement into **ChatGPT** (a "Jacobian
  Challenge" project) for a proof strategy, then into **Grok** for critique,
  iterating until concrete. The strategy paragraph is saved back into the
  blueprint node's `\begin{proof}`. Rationale: "they have different blind spots…
  cross-checking catches silent errors a single-model loop would miss." Many
  chats run in parallel, **per-leaf**.
- **Phase C — bottom-up formalization in cloud sessions.** Launch a **Claude Code
  cloud session** per smallest leaf; the prompt cites the blueprint node
  (label + URL) and the Phase-B strategy, instructs the agent to refine
  internally, formalize bottom-up, and **open a PR when the leaf is closed**.
  Integrate, move up the tree. The "Workers jc0–jc4" are these parallel sessions.

## 3. The agent stack (multi-model by design)

| Role | Agent | Job |
|------|-------|-----|
| Orchestrator | **Claude (main)** | drives the whole pipeline; manages state |
| Strategy | **ChatGPT** + **Grok** | Phase-B proof planning + cross-critique |
| Formalization workers | **Claude Code cloud sessions** (jc0–jc4, parallel) | close one leaf → PR |
| Bounded proving | **Aristotle** (remote Lean prover, via MCP) | local proof goals |
| Top-down rounds | **`codex exec`** (local sub-agent) | refine `Solution.lean` |

Browser tabs (driven via Playwright) stay open for: the **dependency graph** (the
"where's the next gap" surface), Claude Code, ChatGPT, Grok, GitHub. An earlier
mode ran `/loop 15m` timer-ticks (`ref/PROMPT.md`): each tick = one
management-and-progress cycle (consume Aristotle results, refresh the README
progress bar, push) — paused during the A–C blueprint refinement, to resume in
Phase C "driven by the blueprint's leaves rather than ad-hoc sorry selection."

## 4. The blueprint as a live database + the sorry-frontier as the work queue

The blueprint is not just docs — it is the **synced source-of-truth and progress
tracker**, backed by a substantial custom toolchain in `scripts/`:

- **Frontier / sorry management:** `gap-summary.py` (notready/leanok/unflagged
  state of the dep graph), `audit-sorries.py`, `list-sorries.py`,
  `browse-sorries.py`, `diff-sorries.py`, `git-diff-sorries.py`, `find-cycles.py`,
  `find-orphans.py` — the `sorry` set *is* the task queue, kept acyclic and
  orphan-free.
- **Proof application:** `fix-sorries.py`, `patch-sorry.py`, `apply_jc2_proof.py`.
- **Blueprint↔code sync:** `sync-blueprint-db.py`, `blueprint_audit.py`,
  `blueprint_graph_audit.py`, `blueprint_graph_connect.py`,
  `blueprint_graph_patch.py`, `build_collapsible_dep_graph.py`.
- **TeX hygiene:** `lint-tex.py`, `fix_tex_commands.py`, `find-undef-macros.py`.

The deployed graph has a **plain-English ("layman") toggle** and a collapsible,
section-grouped view used as the *live* progress tracker.

## 5. CI gates (`.github/workflows/`)

- `solution-build.yml` — the Lean build (does it compile?).
- `comparator-smoketest.yml` — **kernel-replay comparator** (`comparator/`,
  `lean4export`): the soundness/axiom-hygiene gate that enforces the 0-axiom,
  no-`sorryAx` discipline on the headline.
- `blueprint-audit.yml` — blueprint ↔ code consistency.
- `pages.yml`, `pdf.yml` — deploy the graph + build the formal/plain-English PDFs.

## 6. What this validates — and extends — about Centauro

Our [`centauro.md`](centauro.md) design independently arrived at most of this;
their running system is the proof it works, and shows what we'd need to build:

| Centauro idea | Their realized form |
|---|---|
| Frozen-statement contract | `Challenge.lean` = 24 frozen `sorry`s |
| Blueprint as the catalog/tracker | the synced blueprint DB + gap-summary |
| Subproject = a ready (blue) node | a sorry-frontier leaf, Phase-A-surfaced |
| Cross-model vetting (our Gemini/Codex) | **Phase B: ChatGPT + Grok per leaf** |
| Agent workers (the "Centauri") | parallel Claude Code cloud sessions jc0–jc4 |
| Machine-gated acceptance | solution-build + **comparator** + blueprint-audit |
| Chiron meta-reviewer | (human orchestrator reviews; no separate reviewer) |

**Differences / lessons:**

1. **Plan before formalizing (Phase B) is the part we under-specified.** Their
   explicit per-leaf, two-model strategy step (ChatGPT + Grok) before any Lean is
   exactly the discipline that prevented dead-ends like our σ*-pullback detour. We
   should make "vet the strategy, cross-model, before coding" a first-class step.
2. **The frontier is `sorry`, not `axiom`.** Their 0-axiom rule + the comparator
   gate is a cleaner trust story than our axiom-staging. Their `sorry`-tooling
   (audit/diff/cycles/orphans) is what makes the frontier a usable queue — we have
   the axiom audit but not the equivalent live tooling.
3. **Blueprint-as-database is the engine.** The dep graph must be a *true* gap
   inventory (Phase A's gating signal), synced to code, or it's just an outline.
   Our generated blueprint is a good start but is still an *outline* (axioms as
   leaves), not yet a fully gap-surfaced DAG.
4. **Solo-orchestrated, not community.** They run the "distributed" model with a
   *single* human driving many agents — no external contributors, no claim
   mechanism, no licensing. Centauro's community layer is genuinely additional;
   but the *orchestration* core is what makes throughput, and that is what to
   adopt first.

## 7. Bottom line

tangentstorm is running, today, a mature version of the agent-orchestrated
formalization model: **blueprint-as-gap-DB → cross-model per-leaf planning →
parallel cloud-session formalization → PR-cadence integration → comparator-gated
0-axiom soundness.** Our distinctive assets (concrete curve models, axiom-hygiene
discipline) are complementary; our *process* should borrow their Phase-B
cross-model planning, their live sorry-frontier tooling, and their comparator
gate before scaling our own contribution program.
