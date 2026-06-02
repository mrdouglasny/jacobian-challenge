# Community subprojects program — distributed, agent-friendly contribution

*Authored 2026-06-02. A plan to finish the Jacobian Challenge much faster by
offering many small, self-contained subprojects that external contributors (and
their AI agents) can pick up, complete, and submit as PRs, which we evaluate and
merge. Solicit via the Lean Zulip and the GitHub repo.*

## 0. Why this fits this repo unusually well

The project already produces work in exactly the right unit: **a frozen Lean
statement + a discharge plan with a reading list** (e.g.
[`descent-codex-plan.md`](descent-codex-plan.md),
[`route-d-implementation-plan.md`](route-d-implementation-plan.md), the
per-axiom discharge docstrings). Two more structural advantages:

- **Mechanical acceptance.** Correctness is largely machine-checkable: `lake
  build` is green or not; `#print axioms` lists the trust boundary or not. This
  makes distributed, agent-driven contribution safe in a way most software
  projects are not — a wrong proof simply does not compile.
- **Natural decomposition.** The remaining work is a DAG of lemmas/axioms, each
  small. We already maintain the dependency trace and axiom audit.

The risk inverts the usual one: the danger is not bad code slipping in, it is an
agent **gaming the statement** (weakening it, adding an axiom, hiding a `sorry`).
The whole acceptance design below is built around making that impossible or
trivially detectable.

## 1. The subproject unit

A **subproject** = one GitHub Issue + one row in [`SUBPROJECTS.md`], with a fixed
template. The non-negotiable field is the **frozen statement**.

```
### [subproject] <short-name>            id: SP-NN   difficulty: S|M|L   status: open
Frozen statement (must be proved VERBATIM — name and type unchanged):
    theorem <name> (<binders>) : <type>          -- or `def <name> : <type>`
Location: Jacobians/.../<File>.lean  (append | new file)
Allowed axioms (#print axioms must list ONLY these, beyond the core 3
  propext/Classical.choice/Quot.sound): <list, or "none">
Forbidden: new `sorry`/`admit`/`native_decide`-of-goal; changing the frozen
  signature; weakening hypotheses or strengthening unrelated parts.
Discharge plan: <2–6 lines: strategy + key Mathlib/repo lemmas>.
Reading list (≤4 files, with line ranges): <files>.   # the anti-OOM rule
Reusable infrastructure: <pointers to already-proven lemmas>.
Dependencies: <prerequisite SP-ids, or none>.
Acceptance: lake build green; #print axioms matches "Allowed"; no new sorry;
  signature byte-identical to Frozen statement; mathlib-ready conventions.
```

**Frozen statement = the contract.** It is committed to the repo *first*, as a
`sorry`-stubbed declaration on a tracking branch, so the contributor's only job
is to replace the `sorry`. CI can then assert the declaration's *type* is
unchanged (see §4). This single device defeats almost all statement-gaming.

**Size discipline.** Target S = ≤ ~40 LOC / an afternoon; M = ≤ ~150 LOC; L =
split it further before publishing. The route-D phases and the cross-summand
compat axioms are the model.

## 2. Initial catalog (curated from existing material)

Publish an initial batch of ~12–18, tiered. Sources already in-repo:

**Tier A — good-first-issue (S, self-contained, low context):**
- Small general-analysis lemmas, several already scoped — e.g. the
  "even-analytic = function of `w²`" companion to
  `GeneralResults/OddPartDslope.lean`; growth/Liouville micro-lemmas around
  `EntireGrowth.lean`. Some are even **Mathlib-upstreamable** (extra draw).
- Isolated `simp`/API-completeness lemmas flagged by `#lint`.

**Tier B — axiom discharges (M, the heart of the project):**
- `affineLiftChart_compat_infinityLiftChart` /
  `infinityLiftChart_compat_affineLiftChart` (`EvenAtlas.lean`) — the
  cross-summand Möbius cocycle; **discharge strategy already in the docstrings**.
- Other Class-2 axioms from [`AXIOM_AUDIT.md`](../AXIOM_AUDIT.md) whose discharge
  path is written. Each becomes one SP with its audit row as the spec.

**Tier C — route-D pipeline (M/L, dependency-ordered):**
- P0 `omegaDx_analyticAt` (in progress, maintainer-owned), then **P1 branch
  removability**, **P2 ∞-growth**, **P3 Liouville⇒anti-invariance**, **P4 L2** —
  already spec'd with reading lists in
  [`route-d-implementation-plan.md`](route-d-implementation-plan.md). P1 and P2
  are independent and parallelizable across contributors.

**Tier D — extension sorries (M):** the `Extensions/AbelJacobi.lean` `sorry`s,
each as one SP with a discharge sketch.

Each catalog entry links its discharge doc; we already have a dozen such docs.

## 3. Contributor workflow (→ `CONTRIBUTING.md`)

1. **Claim**: comment `/claim SP-NN` on the issue (or self-assign). Claims expire
   after **7 days** of inactivity to avoid silent blocking; a bot or maintainer
   relabels `status:open`.
2. **Branch & implement**: branch from `main` (or the tracking branch carrying
   the frozen stub); replace the `sorry`; **do not touch the signature**.
3. **Self-verify before PR** (a script we ship, `scripts/check_subproject.sh
   <decl>`): runs `lake build`, prints `#print axioms <decl>`, greps the diff for
   new `sorry`/`admit`, and checks the declaration type matches the frozen one.
4. **PR**: one subproject per PR, title `SP-NN: <name>`, body references the
   issue and pastes the `#print axioms` output. **DCO sign-off** (`Signed-off-by:`
   — `git commit -s`) certifies the contribution under the repo's Apache-2.0
   license; lighter than a CLA, standard for agent-friendly projects.
5. **Agent note** in CONTRIBUTING: "Point your agent at the issue — it is
   self-contained (frozen statement + discharge plan + reading list). Tell it the
   verification rules: validate with `lake build`/`lake env lean`, keep
   `#print axioms` within the allowed set, never add a `sorry` or change the
   signature."

## 4. Evaluation & acceptance (maintainer side)

**Automated gate (CI, must pass before human review):**
- `lake build` green (existing `lean.yml`).
- **Axiom-diff check**: a CI job runs `#print axioms` on the SP's declaration and
  fails if it lists anything outside `[core 3] ∪ Allowed`. (Catches axiom-sneaking
  and hidden `sorryAx`.)
- **No-new-sorry/admit check**: diff scan; fail on added `sorry`/`admit`/`stop`.
- **Frozen-signature check**: assert the declaration's *type* equals the frozen
  one (compare against the stub on the tracking branch, or a checked-in
  `#check @<name>` expected-type test). Defeats statement-weakening.
- **Convention lint**: `#lint` clean (naming, simp-normal-form, unused vars).

**Human review (only on CI-green PRs — small, fast):**
- **Anti-gaming checklist**: signature unchanged ✓; no new axioms beyond Allowed
  ✓; non-vacuity (the proof actually uses its hypotheses; spot-check that the
  statement isn't trivially satisfiable) ✓; no `native_decide`/`decide` bridging
  the math goal ✓; imports add no contradictory/heavy axiom ✓.
- **Proof soundness & style**: skim the proof; mathlib-ready conventions; sensible
  generality. Most of this is cheap because subprojects are small.
- **Headline-adjacent results** (anything feeding the genus theorem): additionally
  run the kernel-replay comparator per [`COMPARATOR.md`] before merge.

**On merge:** update `SUBPROJECTS.md` status → merged; if it discharged an axiom,
update `AXIOM_AUDIT.md` + README counts in the **same** PR (enforced by review);
credit the contributor (`Co-Authored-By` + a `CONTRIBUTORS.md` line).

The automated gate does ~90% of the filtering, so maintainer eval time per
accepted PR is minutes, not hours — the property that makes "finish much faster"
real rather than a review-bottleneck mirage.

## 5. Solicitation

**GitHub (the catalog is the product):**
- README "**Contribute a subproject**" section: 3-line pitch, link to
  `SUBPROJECTS.md` + `CONTRIBUTING.md`, and a one-paragraph "for agents" note.
- Labels: `subproject`, `good-first-issue`, `difficulty:S|M|L`,
  `area:hyperelliptic|axiom|analysis|extension`, `status:open|claimed|in-review`.
- A pinned tracking issue / GitHub **Project board** (columns Open → Claimed →
  In-review → Merged) auto-synced from labels.
- Optional later: GitHub **Pages** rendering of `SUBPROJECTS.md` for a nicer
  landing page.

**Zulip (leanprover.zulipchat.com):**
- An announcement in a project-appropriate stream (e.g. `#new members` for first
  visibility, and a topic in `#Machine Learning for Theorem Proving` given the
  agent angle; consider a dedicated topic under a maths-formalisation stream).
- Post framing: *what* the Jacobian Challenge is + current status (genus theorems,
  axiom count, what's open) + *the offer*: "a catalog of small, self-contained,
  agent-runnable subprojects with frozen statements, discharge plans, and
  machine-checkable acceptance — claim one, point your agent at it, PR it." Link
  the catalog. Emphasize the low-friction, low-risk (CI-gated) nature.
- Cadence: announce **one curated batch** (~12–18) first; restock as they merge;
  post periodic "N subprojects merged, M open" updates to sustain momentum.

## 6. Infrastructure to build (artifact checklist)

1. `CONTRIBUTING.md` — workflow §3 + verification rules + DCO + axiom hygiene.
2. `SUBPROJECTS.md` — the catalog index (table: id, name, difficulty, status,
   deps, discharge-doc link).
3. `.github/ISSUE_TEMPLATE/subproject.yml` — the §1 template as a form.
4. `.github/PULL_REQUEST_TEMPLATE.md` — paste `#print axioms`, confirm
   signature-unchanged, DCO checkbox.
5. CI additions to `.github/workflows/`: axiom-diff job, no-new-sorry job,
   frozen-signature check. (A small Lean script that emits `#print axioms` +
   `#check @name` and a shell wrapper that diffs against expected.)
6. `scripts/check_subproject.sh` — the contributor-side self-verify (build +
   axioms + sorry-scan + signature).
7. `CONTRIBUTORS.md` — attribution.
8. README "Contribute" section + a drafted Zulip announcement.
9. Label set + Project board.

## 7. Risks & mitigations

| Risk | Mitigation |
|------|-----------|
| Statement-gaming (weaken/trivialize) | Frozen stub checked in first; CI signature-equality check |
| Axiom-sneaking / hidden `sorry` | CI `#print axioms` diff vs Allowed; no-new-sorry scan |
| `native_decide`/`decide` bridging math | Lint/grep ban in CI for headline-adjacent SPs; human checklist |
| Duplicate work | `/claim` + 7-day expiry; status labels; Project board |
| Subprojects too big → stall | S/M/L discipline; split any L before publishing |
| Maintainer review bottleneck | Automated gate filters first; keep SPs small; batch reviews |
| Licensing ambiguity | DCO sign-off; Apache-2.0 stated in CONTRIBUTING |
| Dependency tangles | Publish dependency-ordered; gate Tier-C SPs on prerequisites |
| Quality drift / convention rot | `#lint` in CI; mathlib-ready rules linked from each SP |

## 8. Decisions for MRD (defaults proposed)

- **PR base**: `main` directly (recommended) vs a `contrib` integration branch.
- **License/CLA**: DCO sign-off (recommended) vs full CLA vs nothing.
- **Zulip venue**: which stream/topic; whether to also cross-post to the agent/AI
  community.
- **Claim mechanism**: comment-bot vs manual self-assign vs none (first-PR-wins).
- **Comparator scope**: every merged SP vs only headline-adjacent (recommended).
- **First batch size**: ~12–18 (recommended) and which SPs lead.

## 9. Rollout sequence

1. Land the infrastructure (§6 items 1–6) in one PR.
2. Curate + check-in the first batch of frozen stubs (§2); open their issues.
3. README "Contribute" section + Zulip announcement (§5).
4. Run a **pilot** with 2–3 friendly contributors/agents on Tier-A SPs; fix
   friction in CONTRIBUTING/CI.
5. Public announcement of the full batch; restock + status updates on cadence.
