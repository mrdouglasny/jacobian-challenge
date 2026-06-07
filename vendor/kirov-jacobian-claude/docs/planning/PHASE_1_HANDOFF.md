# Phase 1 — handoff to a fresh agent

Self-contained brief for a new agent (Claude / Codex / human) to start
discharging axioms in `jacobian-challenge`. No prior conversation context
needed; everything you need to act is here or one link away.

## 0. What you're inheriting

`jacobian-challenge` has a fully vetted **per-axiom discharge plan tree** at
[`docs/planning/`](.):

- [`ROADMAP.md`](ROADMAP.md) — index of all **90 real axioms** with route /
  effort / Gemini verdict.
- [`CROSS_DOC_ANALYSIS.md`](CROSS_DOC_ANALYSIS.md) — dependency DAG (164
  edges, 18 leaves, 7 cycles with break strategies, top-15 fulcrum, Mermaid
  subgraphs, phased build sequence).
- [`<axiom-slug>.md`](.) — 90 recipe files (statement → why-axiomatized →
  numbered proof recipe with `file:line` citations → files touched →
  acceptance criteria → escalation triggers). Every plan was Gemini 3.1
  Pro vetted; 77 were rewritten in place per the critiques.
- [`_vetting/`](_vetting/) — 90 referee-grade critiques + 4 cross-plan
  cluster audits + raw-results JSON.
- [`dependency-graph.json`](dependency-graph.json) — the dep graph (read it
  if you want to script against the data).
- [`_TEMPLATE.md`](_TEMPLATE.md) — the recipe shape (for reference; don't
  use for new plans, all 90 already exist).

**15 cross-plan inconsistencies** were found and patched into the recipes
on 2026-06-03 (each patched plan carries a `**Cross-plan patch
(2026-06-03):**` note). Read those notes before acting — they are
project-wide invariants you must not re-break.

## 1. Phase 1 scope (this brief)

**Goal**: discharge 4 axioms — the Divisor cluster (3 plans) + the
Wallace-wire validation pick (1 plan) — and prove the toolchain works end
to end: Lean compile + `lean-fleet` gate + axiom-count drop.

Estimated time: **~4 focused days, ~400 LOC across 3 files.**

Why these 4: they are *true leaves* in the dep graph (no project-internal
prereqs), give immediate axiom-count drops, and exercise both wiring
patterns the rest of the project depends on (Mathlib citation + Wallace
vendor citation). Phase-1 success is the green light to start Phase 2
(bridgePath cluster + Hyperelliptic skeleton).

### Phase 1 targets (in execution order)

| # | Plan | Recipe | Verdict | Eff | Wires to |
|---|---|---|---|---|---|
| 1A | `Divisor` | [Divisor.md](Divisor.md) | revise | 1 | Mathlib `FreeAbelianGroup X` |
| 1B | `Divisor.instAddCommGroup` | [Divisor-instAddCommGroup.md](Divisor-instAddCommGroup.md) | revise | 1 | `inferInstance` from 1A |
| 1C | `Divisor.deg` | [Divisor-deg.md](Divisor-deg.md) | **accept** | 1 | Mathlib `FreeAbelianGroup.sum` |
| 1D | `AX_BranchLocus` | [AX_BranchLocus.md](AX_BranchLocus.md) | revise | 4 | Wallace `weightedFiberConservation_of_contMDiff` |

After 1A–1C land, **leverage = 11 downstream plans unblocked** (the whole
sheaf-cohomology layer can finally start in Phase 2/3).

After 1D lands, the Wallace-wiring pattern is validated and the path
opens to `AX_pushforward_pullback`, `pushforwardOneForm`,
`AX_ofCurve_contMDiff` in later phases.

## 2. Per-target instructions

For each target, read the recipe in full before touching code — the
**Proof recipe** section names exact lemmas with `file:line` citations.
The summaries below are pointers, not replacements.

### 1A. `Divisor` (leverage 11, the keystone)

**Source**: `Jacobians/RiemannSurface/LineBundle.lean:51`
**Target form** (per recipe Step 1):
```lean
abbrev Divisor (X : Type u) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] : Type u := FreeAbelianGroup X
```
- All 6 instance binders MUST be preserved (this is Cross-plan Patch A,
  Finding 4 — don't strip them, downstream Lean elaboration depends on them).
- Note `𝓘(ℂ, ℂ)` not `𝓘(ℂ)` (Cross-plan Patch N — the single-arg alias
  causes typeclass-unification failures).
- After replacing `axiom Divisor` with the `abbrev`, downstream plans
  that consume `Divisor X` (PrincipalDivisors, LineBundle, H0, H1,
  canonicalDivisor, abelJacobiDiv, AX_AbelTheorem, AX_RiemannRoch,
  AX_SerreDuality, AX_curve_generates_jacobian, AX_PluckerFormula —
  all 11) start elaborating without further changes.

**Gate check**:
```bash
lake build Jacobians.RiemannSurface.LineBundle
python3 /path/to/lean-fleet/gate.py --repo jacobian-challenge --build Jacobians
# axiom count: 90 -> 89
```

### 1B. `Divisor.instAddCommGroup`

After 1A, this becomes a one-line `inferInstance` (since `FreeAbelianGroup
X` carries `AddCommGroup` natively). Recipe `Divisor-instAddCommGroup.md`
gives the exact term. Don't drop the 6 instance binders.

**Gate check**: axiom count 89 → 88.

### 1C. `Divisor.deg`

`Divisor.deg = FreeAbelianGroup.sum` lifted as an `AddMonoidHom` to `ℤ`.
This is `accept`-verdict — recipe is correct as written, no Gemini revisions
needed. Use Mathlib's `FreeAbelianGroup.lift` directly.

**Gate check**: axiom count 88 → 87.

### 1D. `AX_BranchLocus` (the Wallace-wire validation pick)

**Source**: `Jacobians/Axioms/BranchLocus.lean:100`

This is the prototype "wire to an already-Lean-proven vendored module"
discharge. Read the recipe in [AX_BranchLocus.md](AX_BranchLocus.md) — it
is the most carefully wire-cited plan on the board. Key citations:

- `Jacobians/Vendor/Wallace/HolomorphicForms/HolomorphicMap.lean:1199` —
  `weightedFiberConservation_of_contMDiff` is the heart of the proof.
- `Jacobians/Vendor/Wallace/HolomorphicForms/HolomorphicMap.lean:648` —
  `isHolomorphic_finite_fiber` gives finite-fiber prereq.
- `Mathlib/Topology/LocallyConstant/Basic.lean:326` —
  `IsLocallyConstant.apply_eq_of_isPreconnected` for the
  local-to-global-constant step.

**The "next discrete deliverable"** named in the recipe is a single
~10-line helper `weightedFiberSum_constant_of_contMDiff` to be added
inside the Wallace vendor file (between `:1199` and `end Compatibility`).
Doing this helper first, then the main `AX_BranchLocus` glue, is the
clean order.

**Gate check**: axiom count 87 → 86.

## 3. The lean-fleet gate (run after every discharge)

`lean-fleet` is the orchestration toolkit at a sibling repo. The gate
guarantees you have not regressed:

```bash
cd /<your-checkout-root>/lean-fleet
python3 gate.py --repo jacobian-challenge --build Jacobians
```

What it enforces (hard, exits 1 if violated):
- **No new axioms** — workers may not add an `axiom`. Splitting via a
  helper axiom is can-kicking and was explicitly flagged in cross-plan
  finding 5 (needs-infra cluster).
- **No net new sorries** — net delta of `sorry` count must be ≤ 0.
- **No `import Mathlib`** — no broadened bare imports.
- **Build green** — `lake build Jacobians` must succeed.

Run it after each commit, not just at the end. The gate doesn't run inside
your IDE; you must invoke it.

## 4. Cross-plan invariants (DO NOT re-break)

The 15 cross-plan patches landed on 2026-06-03 are project-wide
constraints. Violating any of them will collide with another plan
downstream. The full set is in
[`_vetting/CROSS_PLAN_CONSISTENCY*.md`](_vetting/); summary:

1. **No `.sheaf` projection on `LineBundle`.** `LineBundle D` is a `PUnit`
   token; H0/H1 are built from the divisor `D` argument directly.
2. **All manifold-model-space uses are `𝓘(ℂ, ℂ)`**, never `𝓘(ℂ)`. The
   single-arg alias is retired project-wide.
3. **`PartialHomeomorph`, not `OpenPartialHomeomorph`.** The latter was a
   hallucinated namespace.
4. **`Divisor` keeps all 6 manifold/topology instance binders.** Don't
   strip them in instance signatures.
5. **`H1` is `Additive (Abelianization (FundamentalGroup X x₀))`** — the
   bare multiplicative `Abelianization` won't satisfy `AddCommGroup`.
6. **Hyperelliptic equivalences stay `≃ₜ`**, not biholomorphism. The
   genus plan promotes locally.
7. **Path-integration backend is the Kirov bridge** (`Bridge/KirovLineIntegral`).
   No scratch `pathIntegralAnalyticArc` route.
8. **Intersection-form companion theorems remain top-level** (do not delete
   them in favour of a bundled typeclass).
9. **`abelJacobiDiv` takes an explicit basepoint** (no `Classical.choice`
   for the integration anchor).
10. **`AX_curve_generates_jacobian` needs `AX_SerreDuality`** (was wrongly
    dropped pre-vetting).

Plus the 5 patches you're directly enforcing in Phase 1 (Findings 3, 4
about Divisor cycle + binders; Finding 2 about LineBundle/H1; Finding 5
about chart-transition staleness).

## 5. Worker prompt template (for spawned subagents)

If you delegate any single discharge to a worker:

```
You are discharging exactly one axiom in jacobian-challenge.

PLAN: /Users/<...>/jacobian-challenge/docs/planning/<slug>.md
SOURCE FILE: /Users/<...>/jacobian-challenge/<src-path>

Procedure:
  1. Read the plan file IN FULL. The "Proof recipe" section names exact
     lemmas with file:line citations; the "Files touched" lists every
     edit. Follow them.
  2. SEARCH FIRST. Grep <root>/catalogs/ALL_LEMMAS.tsv and the cited
     supporting files (Vendor/Wallace/*, Vendor/Kirov/*, Mathlib paths)
     to confirm every cited decl name still exists and matches the
     signature in the recipe. If a decl moved or was renamed, stop and
     report — do NOT invent a substitute.
  3. Make the edits listed in "Files touched". DO NOT touch any file
     outside that list except `catalogs/`.
  4. Build the narrowest target: `lake build <module>`.
  5. Run the gate: `python3 <lean-fleet-root>/gate.py --repo
     jacobian-challenge --build Jacobians`. If it exits 1, fix the
     specific violation; never `--no-verify` or add a helper axiom.

Forbidden:
  - Adding any `axiom`.
  - Adding `import Mathlib` (bare) or a new `import Mathlib.X` not in
     the recipe's "Files touched" list.
  - Weakening or renaming any public declaration.
  - Using `aesop` / `grind` / broad `simp_all` unless the recipe says so.

Return: the diff, the build result, the gate report. If genuinely
blocked, return a BLOCKER note naming the missing piece — do not stub.
```

## 6. Escalation triggers (stop and report)

Stop and surface to a human if any of these happen:

- **The axiom needs to be kept.** If you conclude during discharge that the
  axiom is genuinely required (cannot be proven without itself or another
  axiom), this is a reserved human authority — do not silently keep it.
  See [`README.md`](../../README.md) "Reserved human authorities".
- **A public statement needs to change.** Any signature touched on a
  declaration used by another file/repo is a reserved decision.
- **A cited Mathlib / Wallace / Kirov decl is missing or has drifted.**
  Stop, name it, escalate. Do not improvise a substitute.
- **The gate keeps failing on the same constraint after 3 honest fix
  attempts.** Something structural is wrong; surface it.
- **Toolchain bump or `Mathlib` version change implied.** Always human-decided.

## 7. After Phase 1 — pointers to Phase 2 / 3

Once Phase 1 lands (axiom count 90 → 86 in jacobian-challenge), the
recommended next waves are:

- **Phase 2 — bridgePath cluster** (~1 week, ~700 LOC). Discharge
  `bridgePath` as a real `def` per [bridgePath.md](bridgePath.md). This
  unblocks the 5 derived `bridgePath_*` axioms (all `accept` or short
  `revise` per Gemini), the `loopIntegralToH1` plan, and validates the
  Kirov-wire pattern across `Vendor/Kirov/LineIntegral.lean`.
- **Phase 3 — Hyperelliptic skeleton**. Discharge `Hyperelliptic` via
  parity dispatch (`docs/hyperelliptic-atlas-plan.md` has the design),
  which collapses the 5-instance + 2-homeo cluster (Cycle 5 in
  [`CROSS_DOC_ANALYSIS.md`](CROSS_DOC_ANALYSIS.md)). ~1 day for the type
  itself; the chart/manifold instances are weeks beyond that.
- **Phase 4 — sheaf-cohomology layer**. The big one. `PrincipalDivisors`,
  `LineBundle`, `H0`, `H1`, `canonicalDivisor`. Multi-month. Unblocks
  RiemannRoch / SerreDuality / Plücker / AbelTheorem /
  curve_generates_jacobian.

[`CROSS_DOC_ANALYSIS.md`](CROSS_DOC_ANALYSIS.md) §Phased build sequence
gives the full ordering. You can also script against
[`dependency-graph.json`](dependency-graph.json) to compute "what unblocks
the most" for any candidate.

---

**Reading order for fastest ramp** (≤30 min):
1. [`../../README.md`](../../README.md) §Axiom hygiene → §Per-axiom discharge plans.
2. [`ROADMAP.md`](ROADMAP.md) — verdict tally + the full per-axiom table at bottom.
3. This file.
4. The recipe for whichever Phase 1 target you start on.
5. (Optional) Skim the cycles section of [`CROSS_DOC_ANALYSIS.md`](CROSS_DOC_ANALYSIS.md) so the bigger graph is in your head.
