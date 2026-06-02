# Subproject spec — format convention

*Draft for review, 2026-06-02.* Conventions for a **subproject** — a
self-contained, claimable unit of contribution in the distributed effort
(program: [`centauro.md`](centauro.md); theming parked, neutral terms here). A
subproject's spec file is simultaneously its **contract** (the frozen statement
to prove) and its **discharge plan**.

**This doc is consistent with — and a superset of —**
[`~/.claude/AXIOM_AUDIT_FORMAT.md`](AXIOM_AUDIT_FORMAT) (the axiom-audit / discharge-plan
standard). It reuses that doc's Rating scale, Vetting source-codes, discharge-plan
structure, and same-commit discipline, and adds the fields a distributed/agent
contribution needs (frozen statement, allowed-axiom set, reading list, status,
acceptance gate). *(Repo-local for now; may be promoted to a global format doc
once stable, like the axiom-audit standard.)*

---

## Relationship to the axiom-audit standard (no divergence)

- **Reused verbatim** from `AXIOM_AUDIT_FORMAT.md`: the **Rating** scale
  (`Standard` / `Likely correct` / `Needs review` / `Placeholder` / `Flagged`),
  the **Vetting** source-codes (`DT` / `GR` / `CX` / `LP` / `SA` / `PR`), the
  discharge-plan-doc body (Goal · API-to-reuse with file:line · step outline with
  intermediate lemma signatures · acceptance · codex hand-off notes), and the
  **same-commit updating discipline**.
- **One file, two roles.** If a subproject discharges an axiom, its spec file
  **is** the `docs/<axiom-name>-discharge-plan.md` that `AXIOM_AUDIT.md` would
  otherwise link to. The audit row's `Strategy / Plan` column links to the SP
  spec; do **not** maintain two separate docs.
- **The superset:** `SP spec = discharge-plan-doc + {frozen statement, allowed
  axioms, reading list, difficulty, status, dependencies, CI acceptance gate}`.

---

## File location & layout

- **Index**: `docs/subprojects.md` — a **table only** (no inlined specs), a
  primary-visibility catalog like `AXIOM_AUDIT.md`.
- **Per-unit spec**: `docs/subprojects/SP-NN-<slug>.md` — **one file per unit**.
- **Cross-links**: axiom-discharge SP ↔ its `AXIOM_AUDIT.md` row; object-contract
  SP ↔ `docs/contracts/`; pipeline SPs ↔ their design doc (e.g.
  `route-d-implementation-plan.md`).

---

## ID, naming, tiers, status

- **ID**: `SP-NN`, sequential, never reused.
- **Slug**: kebab-case, from the target declaration name.
- **Tier** (difficulty/role bucket): **A** good-first / upstreamable · **B** axiom
  discharge · **C** pipeline (dependency-ordered) · **D** extension sorry.
- **Difficulty**: `S` (≤~40 LOC / an afternoon) · `M` (≤~150 LOC) · `L` (split
  before freezing).
- **Status lifecycle**: `draft` (statement not yet frozen/vetted) → `ready`
  (frozen + vetted, claimable) → `claimed` → `in-review` → `merged`. Side states:
  `blocked` (deps unmet), `parked`.

---

## The spec template (canonical fields)

```markdown
# SP-NN — <title>

**Tier** <A|B|C|D> · **Difficulty** <S|M|L> · **Status** <…> · **Deps** <SP-ids | none>

## Frozen statement
*Must be proved VERBATIM — declaration name and type unchanged.* Stubbed at
`<file>:<line>` (namespace `<…>`):
```lean
theorem <name> (<binders>) : <type>        -- or `def <name> : <type>`
```

## Allowed axioms
`#print axioms <name>` must list only `[propext, Classical.choice, Quot.sound]`
∪ `<these>`. Default: none. <if any, name + why permitted>

## Statement vetting   (Phase A — before freezing; reuses the axiom protocol)
**<Rating>** (`<Vetting codes>`, <model/date if Gemini/Codex>). Stub type-checks;
cross-vetted for non-vacuity / right generality / sufficient hypotheses; MRD
meta-approved.

## Goal & effort
<plain-language goal; effort estimate; what discharging it buys (e.g. retires
axiom X / unblocks SP-M)>.

## Discharge plan
<step-by-step outline with intermediate lemma signatures>.

## Existing API to reuse
<repo/Mathlib lemmas with file:line pointers>.

## Reading list   (≤4 files, with line ranges — the anti-OOM rule)
<files:line-ranges>.

## Acceptance
`lake build` green; `#print axioms <name>` ⊆ Allowed; no new `sorry`/`admit`;
frozen signature byte-identical; `#lint` clean; no `native_decide`/`decide` of the
goal. (Headline-adjacent: also the kernel-replay comparator.)

## Consumers / why it matters
<downstream theorems; load-bearing links>.

## Notes for agent / Codex hand-off
<gotchas; verification commands; CLAUDE.md pre-push rule>.
```

---

## Index (catalog) row format

`docs/subprojects.md` uses one table:

```markdown
| ID | Title | Tier | Diff | Status | Deps | Spec |
|----|-------|------|------|--------|------|------|
| SP-1 | affineLiftChart_compat_infinityLiftChart | B | L | ready | — | [SP-1](subprojects/SP-1-affine-infinity-compat.md) |
```

Anchored `File:Line` links use the `AXIOM_AUDIT_FORMAT.md` style:
`[`EvenAtlas.lean:243`](../Jacobians/ProjectiveCurve/Hyperelliptic/EvenAtlas.lean#L243)`.

---

## Inline vs break out

**Always one spec file per unit** — every SP spec exceeds the 2–3-sentence
inline threshold of `AXIOM_AUDIT_FORMAT.md`, so it lives in `docs/subprojects/`,
never inlined in the index. *(This supersedes the interim inlining of SP-1/SP-2
in `subprojects.md`, which is being split out.)*

---

## Updating discipline (mirrors the audit standard)

- **Same-commit rule**: adding, freezing, restating, or merging an SP updates the
  **index row** — and, if it discharges an axiom, the `AXIOM_AUDIT.md` row +
  README counts — **in the same commit**.
- **Per-freeze**: `draft → ready` only after Phase-A vetting (stub type-checks,
  cross-vet, MRD meta-approval); record the Rating/Vetting in the spec.
- **Per-merge**: status → `merged`; if it discharged an axiom, move that audit row
  to `Recently discharged` with a proof file:line pointer.
- **On rename/move**: chase every reference (index, spec, audit, dependents). The
  catalog names the units; if the declaration name changes, the frozen statement
  and all links must too.

---

## Examples (to be instantiated)

- **SP-1** `affineLiftChart_compat_infinityLiftChart` — Tier-B axiom-discharge
  exemplar (its spec file doubles as the discharge-plan doc linked from
  `AXIOM_AUDIT.md`).
- **SP-8** even-analytic-factors-through-`w²` — Tier-A upstreamable exemplar.
