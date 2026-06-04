# Phase 2 — Hyperelliptic parity-dispatch sweep

Continuation of [`PHASE_1_HANDOFF.md`](PHASE_1_HANDOFF.md). Discharges the
**Hyperelliptic cluster** (Cycle 5 from
[`CROSS_DOC_ANALYSIS.md`](CROSS_DOC_ANALYSIS.md) — 6 mutually-blocking
nodes that the cycle-break guidance says to break by discharging the
unified type first via parity dispatch).

## 0. Preconditions

Phase 1 should be **complete and on `origin/main`** before starting:

- `Divisor` is a real `abbrev` to `FreeAbelianGroup X` in
  `Jacobians/RiemannSurface/LineBundle.lean:51` (with all 6 manifold/topology
  binders preserved).
- `Divisor.instAddCommGroup`, `Divisor.deg` are real instances/`AddMonoidHom`s.
- `AX_BranchLocus` is a real `theorem`, with the helper
  `weightedFiberSum_constant_of_contMDiff` added inside
  `Jacobians/Vendor/Wallace/HolomorphicForms/HolomorphicMap.lean`.
- `lean-fleet` gate reports **axiom count 86** for jacobian-challenge,
  build green on `lake build Jacobians`.

If any of these is not done, finish Phase 1 first — this phase relies on
the toolchain validation Phase 1 provides.

## 1. Phase 2 scope

**Goal**: discharge the 8 axioms in the unified-`Hyperelliptic` cluster by
breaking Cycle 5 via parity-dispatch on `H.f.natDegree`. After Phase 2 the
unified `Hyperelliptic` type is a real `def`, all 5 typeclass-instance
axioms are real `instance`s, and the two parity-homeo axioms collapse to
`rfl`-class proofs.

Estimated time: **~1 focused week, ~250 LOC, all in
`Jacobians/ProjectiveCurve/Hyperelliptic.lean` plus a small parity-helper
file.**

Axiom count drop: **86 → 78**.

The cluster discharged here is **bounded by what the parity dispatch
itself can do**. The two heavy `Hyperelliptic` axioms NOT in this phase
(`instChartedSpace`, `instIsManifold`) require the substantial atlas
work — they are `needs-infra` and live in Phase 4+.

### Phase 2 targets (in execution order)

| # | Plan | Recipe | Verdict | Pre-vet eff | Wires to |
|---|---|---|---|---|---|
| 2A | `Hyperelliptic` | [Hyperelliptic.md](Hyperelliptic.md) | revise | 5 | parity dispatch over `HyperellipticOdd` / `HyperellipticEvenProj` (both already real types) |
| 2B | `AX_Hyperelliptic_oddEquiv` | [AX_Hyperelliptic_oddEquiv.md](AX_Hyperelliptic_oddEquiv.md) | revise | 4 | `Equiv.cast` (Mathlib) on `dif_pos h` |
| 2C | `AX_Hyperelliptic_evenEquiv` | [AX_Hyperelliptic_evenEquiv.md](AX_Hyperelliptic_evenEquiv.md) | **accept** | 2 | `Equiv.cast` on `dif_neg h` |
| 2D | `Hyperelliptic.instTopologicalSpace` | [Hyperelliptic-instTopologicalSpace.md](Hyperelliptic-instTopologicalSpace.md) | revise | 0 (subsumed) | constructed inside 2A (Step 3 of the Hyperelliptic recipe) |
| 2E | `Hyperelliptic.instT2Space` | [Hyperelliptic-instT2Space.md](Hyperelliptic-instT2Space.md) | revise | 1 | `Homeomorph.t2Space` (Mathlib) through `oddEquiv` / `evenEquiv` |
| 2F | `Hyperelliptic.instCompactSpace` | [Hyperelliptic-instCompactSpace.md](Hyperelliptic-instCompactSpace.md) | **accept** | 1 | `Homeomorph.compactSpace` (Mathlib) through equiv |
| 2G | `Hyperelliptic.instConnectedSpace` | [Hyperelliptic-instConnectedSpace.md](Hyperelliptic-instConnectedSpace.md) | **accept** | 1 | `Homeomorph.connectedSpace` (Mathlib) through equiv + `AX_HyperellipticAffine_connected` |
| 2H | `Hyperelliptic.instNonempty` | [Hyperelliptic-instNonempty.md](Hyperelliptic-instNonempty.md) | revise | 1 | `Equiv.nonempty` through equiv |

**Cycle-break rationale.** [`CROSS_DOC_ANALYSIS.md`](CROSS_DOC_ANALYSIS.md)
Cycle 5 (6 nodes) instructs: discharge `Hyperelliptic` first via
`dite (Odd H.f.natDegree) (λ h => HyperellipticOdd H h) (λ h => HyperellipticEvenProj H)`.
Once that `def` exists, the two homeos collapse to `rfl` / `Equiv.cast`
and the 5 prop-valued instances inherit through the homeos. This is the
**break before recipe** — the per-plan `**Blocked by:**` fields were
written conservatively before the cycle analysis and treat the type and
its instances as mutually-depending. The cycle-break supersedes them.

## 2. Per-target instructions

### 2A. `Hyperelliptic` — the parity-dispatch `def`

**Source**: `Jacobians/ProjectiveCurve/Hyperelliptic.lean:59`

Replace the `axiom Hyperelliptic` block with the real `def`:

```lean
noncomputable def Hyperelliptic (H : HyperellipticData) : Type :=
  dite (Odd H.f.natDegree)
    (fun h => HyperellipticOdd H h)
    (fun h => HyperellipticEvenProj H)
```

Both branches already exist as real types in the project
(`Hyperelliptic/Basic.lean` for `HyperellipticOdd`,
`Hyperelliptic/Even.lean` for `HyperellipticEvenProj`).

The recipe's stated `**Blocked by:**` mentions `instChartedSpace` and
`instIsManifold` — **ignore that for the `def` itself**. The chart /
manifold instances are downstream consumers, not prerequisites for the
type definition. The `def` itself depends only on the two parity-specific
types, which are already real.

**Discharges in this step**: `Hyperelliptic` and (because Step 3 of the
recipe constructs it inline) `Hyperelliptic.instTopologicalSpace`.

Axiom count: 86 → 84.

### 2B–2C. `AX_Hyperelliptic_oddEquiv` and `_evenEquiv` — the homeos

Once 2A lands, both homeo axioms collapse. The parity-specific case
selector inside the `dite` makes the equivalence a literal type-cast:

```lean
theorem AX_Hyperelliptic_oddEquiv (H : HyperellipticData) (h : Odd H.f.natDegree) :
    Hyperelliptic H ≃ₜ HyperellipticOdd H h := by
  unfold Hyperelliptic
  exact ⟨Equiv.cast (dif_pos h), continuous_id.congr (fun _ => rfl), continuous_id.congr (fun _ => rfl)⟩
```

Symmetric for `_evenEquiv` with `dif_neg`. The recipes give the exact
term; the topology continuity for `Equiv.cast` is folklore in Mathlib
once the underlying types are equal.

**Cross-plan constraint (Patch E)**: keep these as `≃ₜ` Homeomorph, **NOT**
biholomorphism. Analytic promotion is deferred to `AX_Hyperelliptic_genus`
via a manifold-transport lemma; do not change the signatures here.

Axiom count: 84 → 82.

### 2D. `Hyperelliptic.instTopologicalSpace` (subsumed)

This plan was marked `**SUBSUMED**` in Patch L — the `TopologicalSpace`
instance is constructed inside step 3 of plan 2A
(`TopologicalSpace.induced (Equiv.cast <| dif_pos h) inferInstance`,
case-split by parity). If 2A is done correctly, this axiom is replaced
without further work; just verify with `#print axioms` that it no longer
shows in the closure.

Axiom count: 82 → 81.

### 2E. `Hyperelliptic.instT2Space`

After 2A + 2B + 2C land, this becomes a one-line case-split:

```lean
instance Hyperelliptic.instT2Space (H : HyperellipticData) : T2Space (Hyperelliptic H) := by
  by_cases h : Odd H.f.natDegree
  · exact (AX_Hyperelliptic_oddEquiv H h).symm.t2Space
  · exact (AX_Hyperelliptic_evenEquiv H h).symm.t2Space
```

Same shape for 2F (`CompactSpace`), 2G (`ConnectedSpace`), 2H (`Nonempty`).
`HyperellipticOdd` and `HyperellipticEvenProj` both have their
instances proved in `Hyperelliptic/Basic.lean` and `Hyperelliptic/Even.lean`
respectively; pulling them through the homeo is the entirety of the proof.

For 2G (`instConnectedSpace`) the proof also needs
`AX_HyperellipticAffine_connected`, which remains a `needs-infra` axiom
in Phase 2 — discharging the affine-connected axiom is its own task
(Phase 3 candidate). The instance plan can land **assuming**
`AX_HyperellipticAffine_connected` is still an axiom and citing it as a
project decl; this is consistent with the cross-plan invariants because
no helper axiom is being introduced.

Axiom count: 81 → 78.

## 3. Cross-plan invariants (still binding from Phase 1)

All 10 invariants from [`PHASE_1_HANDOFF.md`](PHASE_1_HANDOFF.md) §4
remain in force. The four most relevant to Phase 2:

- **Manifold-model notation is `𝓘(ℂ, ℂ)`**, not `𝓘(ℂ)`. (Patch N. Anything
  you write referencing a model space in this cluster must use the
  two-argument form.)
- **Hyperelliptic equivalences stay `≃ₜ`** (Patch E), not biholomorphism.
- **No new `axiom`s.** If you find you need one, stop and escalate. The
  Hyperelliptic cluster is supposed to fall out of the dispatch without
  introducing anything new.
- **Don't strip instance binders.** All Hyperelliptic instances inherit
  the `HyperellipticData` parameter; preserve any further `[…]` binders
  the recipe states.

## 4. Gate check after each discharge

```bash
cd <your-checkout-root>/lean-fleet
python3 gate.py --repo jacobian-challenge --build Jacobians
```

Expected per-step axiom-count drops:

| Step | 2A+2D | 2B | 2C | 2E | 2F | 2G | 2H |
|---|---|---|---|---|---|---|---|
| count after | 84 | 83 | 82 | 81 | 80 | 79 | 78 |

(2A discharges Hyperelliptic AND Hyperelliptic.instTopologicalSpace
inline, hence the double drop.)

If a gate failure says "new-axiom: …" check whether you accidentally added
a stub for a non-Hyperelliptic-cluster dep. Don't paper over with a
helper axiom — escalate.

If the build fails with a typeclass-synthesis error like
`failed to synthesize T2Space (Hyperelliptic H)`, the instance you wrote
for that property isn't being picked up — usually a missing `instance`
keyword, or the binder context dropped one of `HyperellipticData`'s
implicit assumptions. Read the local context, don't reach for a workaround.

## 5. Worker prompt template

If you delegate a single discharge to a worker subagent (recommended for
the per-instance proofs 2E–2H, which are uniform):

```
You are discharging exactly one axiom in jacobian-challenge.

PLAN: /Users/<...>/jacobian-challenge/docs/planning/<slug>.md
SOURCE FILE: /Users/<...>/jacobian-challenge/Jacobians/ProjectiveCurve/Hyperelliptic.lean
PRECONDITION: The unified `Hyperelliptic` type is already a real `def`
via `dite` over `Odd H.f.natDegree`. The two homeos
`AX_Hyperelliptic_oddEquiv` and `_evenEquiv` are already real theorems.

Procedure:
  1. Read the plan IN FULL.
  2. Replace `axiom Hyperelliptic.inst<X>` with `instance Hyperelliptic.inst<X>`
     using a one-line case-split through `AX_Hyperelliptic_oddEquiv` /
     `_evenEquiv` and the underlying `HyperellipticOdd` / `HyperellipticEvenProj`
     instance. The recipe gives the exact term.
  3. `lake build Jacobians.ProjectiveCurve.Hyperelliptic`.
  4. Run the lean-fleet gate; verify axiom count drops by 1.

Forbidden:
  - Adding any `axiom`.
  - Touching any file outside `Jacobians/ProjectiveCurve/Hyperelliptic.lean`
    and its `Basic.lean` / `Even.lean` siblings (the homeos are defined
    in `Hyperelliptic.lean`; the parity-specific instances they lift
    through live in the siblings).
  - Changing the homeo signatures from `≃ₜ` to anything else.

Return: the diff, the build result, the gate report.
```

## 6. Escalation triggers (Phase 2-specific)

Beyond the general triggers in [`PHASE_1_HANDOFF.md`](PHASE_1_HANDOFF.md) §6:

- **`Equiv.cast` doesn't elaborate** because the two parity-specific
  types differ in some implicit-argument shape. This is a real risk; if
  you hit it, surface the exact `cast` failure and the goal state.
  Workarounds via `cast_heq` / `HEq.subst` are acceptable; ad-hoc parity
  splits at every use site are not.
- **`HyperellipticEvenProj` doesn't have the instance** you're trying to
  lift through. Confirm in `Hyperelliptic/Even.lean` — if the instance
  is genuinely missing on the parity-specific type, fix it there first
  rather than papering over here.
- **Cycle 5 didn't actually break.** If after 2A the recipe-stated
  `Blocked by:` chain still triggers (e.g. `instChartedSpace` is somehow
  needed for the `def`), reread the cycle-break guidance in
  `CROSS_DOC_ANALYSIS.md` and report what you observe.

## 7. What Phase 2 leaves on the table — Phase 3 pointers

After Phase 2, axiom count is 78. The next-most-impactful clusters:

- **Phase 3 — `bridgePath` and the Kirov line-integration layer** —
  ✅ **DONE (2026-06-04, branch `phase2-bridgepath`).** `bridgePath`
  is now a real `def` backed by the new `Bridge/BridgePath.lean`
  smooth-path-connectedness infrastructure (~1450 LOC: flat-segment
  calculus → manifold path-source → Lebesgue chart-subdivision →
  `Path.trans` concatenation → unconditional chart-differentiability),
  and **all five derived axioms** — `bridgePath_continuous`,
  `bridgePath_chart_differentiable`, `bridgePath_at_zero`,
  `bridgePath_at_one`, and `bridgePath_lineIntegrable` (the
  integrand-continuity fact, from continuity of `pathSpeed`) — are now
  theorems. The **entire 6-axiom cluster is discharged.** This took ~1
  session via background Codex, not ~3 weeks. Still to wire onward:
  `loopIntegralToH1` and `pathIntegralBasepointFunctional` (per
  cross-plan Patch K). Axiom drop on this branch: 86 → 80.
- **Phase 4 — Hyperelliptic atlas** (`instChartedSpace` +
  `instIsManifold` + the IFT cluster). The work Phase 2 deliberately
  deferred. `needs-infra`, weeks-to-months, mostly in
  `OddAtlas/InfinityChart.lean` and `Hyperelliptic/AffineForm.lean`.
- **Phase 5 — sheaf-cohomology layer**. The multi-month one
  (`PrincipalDivisors`, `LineBundle`, `H0`, `H1`, `canonicalDivisor`),
  which then unblocks the keystone classical theorems
  (`AX_RiemannRoch`, `AX_SerreDuality`, `AX_PluckerFormula`,
  `AX_AbelTheorem`, `AX_curve_generates_jacobian`). The single
  highest-leverage downstream payoff in the project.

[`CROSS_DOC_ANALYSIS.md`](CROSS_DOC_ANALYSIS.md) §"Phased build
sequence" gives the full ordering, and
[`dependency-graph.json`](dependency-graph.json) is the script-readable
artifact for computing leverage scores yourself.

---

**Reading order for fastest Phase 2 ramp** (≤30 min):

1. Confirm Phase 1 is done (run the gate, axiom count = 86).
2. [`CROSS_DOC_ANALYSIS.md`](CROSS_DOC_ANALYSIS.md) §"Cycle-breaking
   guidance" → Cycle 5. The dispatch-then-instances-then-homeos order
   only makes sense if you've internalised the cycle break.
3. This file.
4. [`Hyperelliptic.md`](Hyperelliptic.md) — the recipe for 2A. The other
   7 plans (2B–2H) are uniform once 2A's pattern is in your head.
5. The two underlying recipes in `Hyperelliptic/Basic.lean` and
   `Hyperelliptic/Even.lean` for the inherited instances (skim — you
   only need to know they exist and what they're named).
