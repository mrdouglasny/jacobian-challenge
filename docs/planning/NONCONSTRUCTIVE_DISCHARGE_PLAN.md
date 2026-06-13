# Non-constructive discharge plan — the last axiom and the Albanese universality

*2026-06-13. Supersedes the constructive T-GEN program as the primary route.*

## The pivot, in one paragraph

We spent the endgame trying to discharge `AX_PeriodCycleBasis` **constructively**
— exhibit an explicit integral homology basis (cycle basis), which forced
"analytic loops generate H₁" (T-GEN) and from there the Mathlib-absent
approximation theorems Whitney and Grauert. Studying Kirov's submission
(`../jacobian-claude`, comparator-clean: Buzzard's 24 sorry-free **and**
axiom-free) showed this was **the harder route, and unnecessary**. Kirov never
exhibits cycles. He proves the period lattice is a genuine rank-2g lattice
**non-constructively** — discreteness + non-degeneracy ⟹ `ZLattice` ⟹ a basis
exists — and that suffices for the whole challenge. This document is the
discharge plan that follows his route, reimplemented as our own (per the
no-vendoring rule: ideas with citation, implementation ours).

## Why the constructive route was against the grain

A period lattice is by definition the analytic image of `H₁(X,ℤ)`. The
challenge (and the Albanese universal property) only ever needed the lattice to
**exist as a full-rank lattice** — never to come with named generators. Two
facts about the *period pairing*, both provable by classical complex analysis,
give exactly that:

| Fact | Argument | Our status |
|---|---|---|
| **Discreteness** of the lattice | isolated-zero / residue (Forster 21.4(b)) | **PROVEN** (K-LITE, `discreteTopology_loopPeriodLattice`, unconditional) |
| **Non-degeneracy** (real span = ⊤) | maximum principle: a form with all periods 0 has a single-valued primitive, hence vanishes (Forster 21.4(c)) | **MISSING** — this is the one lemma to port |

Discreteness + non-degeneracy ⟹ `IsZLattice` ⟹ Mathlib's `ZLattice` theory
hands back a rank-2g `ℝ`-basis *by existence*. No cycle basis, no T-GEN, no
Whitney, no Grauert, and — crucially — **no R1/R2**: the Riemann bilinear
relations are the *polarization* data (period matrix symmetric + `Im` positive
definite), which make the Jacobian a principally-polarized abelian variety.
Buzzard's 24 ask for a complex torus + Abel–Jacobi, **not** a ppav, so R1/R2 are
over-strength for the challenge. (Our `PeriodCycleBasis` bundles them; that is
why our `AX_PeriodCycleBasis` is stronger than the headlines need — see
`periodCycleBasis_of_tgen` in #245, whose residual set bottoms out at exactly
R1/R2.)

## G1–G4: the discharge targets (from `VALIDATION.md`)

The validation goal is `ofCurve_isJacobian` (the Albanese universal property)
sorry-free **and** axiom-clean. It rests on four project axioms; **all four**
yield to the non-constructive family — none needs the constructive walls.

### G1 — `AX_PeriodCycleBasis` (the lattice)
- **Route:** port the non-degeneracy lemma (our analog of
  `span_real_truePeriodLattice_eq_top`). Combine with the already-proven K-LITE
  discreteness → `IsZLattice` → basis by existence.
- **Refactor needed:** the headlines (`ofCurve_inj`, functoriality) consume
  `AX_PeriodCycleBasis` via the full `PeriodCycleBasis` structure (with R1/R2).
  Check that they only need the **lattice** (full-rank torus), not the
  polarization. If so, retarget them at a **leaner lattice object** (Kirov-style)
  and drop R1/R2 from the critical path. This is the main engineering step.
- **Open question to settle first:** does `ofCurve_inj` logically need R1/R2, or
  only discreteness + non-degeneracy? (Almost certainly only the latter —
  injectivity is Abel's theorem + a genuine lattice, not the polarization.)

### G2 — `AX_curve_generates_jacobian`  (`closure (range (ofCurve x₀)) = ⊤`)
- **This is a non-degeneracy statement**, the same family as G1. The AJ image
  generates the torus iff it is not trapped in a proper subtorus iff the `g`
  holomorphic forms are independent on it. Same tool as the period
  non-degeneracy; shared work with G1.

### G3 — `AX_period_functoriality`  (`Λ_X ≤ comap (f*-dual) Λ_A`)
- **Pure naturality**: pullback-of-forms sends X-periods into the target torus's
  lattice. We already built the **developing-value naturality engine** (it
  discharged `pushforward`/`pullback`). Derivable from machinery in hand.

### G4 — `AX_torus_self_albanese`  (a complex torus is its own Albanese)
- The Yoneda **base case**: holomorphic, basepoint-preserving maps between
  complex tori are affine group homs. Classical proof over the universal cover
  `ℂ^m → A` (lift, bounded derivatives by compactness ⟹ Liouville ⟹ affine).
  Non-constructive, textbook, ~few hundred Lean lines. **The load-bearing new
  piece** — Mathlib has complex-torus scaffolding but likely not this theorem.

## Why the universal property is the *natural* home for this style

Existence of the Jacobian-as-torus (G1) and its characterization (the universal
property, G2–G4) are **both inherently non-constructive**: one gets the lattice
from non-degeneracy + abstract `ZLattice`, the other gets the factorizing
hom from Yoneda + non-degeneracy. The validation artifact (definition +
anti-vacuity lemmas + universal property) is most naturally proven
non-constructively throughout. The constructive T-GEN program was the one part
fighting the grain.

## Status of the constructive program (parked, not deleted)

All proven and on `main`, valid Lean, retained as a recorded alternative:
- `AnalyticApproxGeneration` (AAW → T-GEN), `TGenFinalReduction`
  (T-GEN ⟸ {Whitney, Grauert}), `ChartLocalHomotopy` + `SmoothLoopApprox`
  (continuous→smooth), `SmoothAnalyticLoop` (smooth→analytic, analytic case free),
  `Index2KernelGeneration` + `BranchCutCoveringBridge` (hyperelliptic via
  `PunctureFillData`), `periodCycleBasis_of_tgen` (#245).
- **Do not invest further** in Whitney / Grauert / π₁-van-Kampen: confirmed
  multi-week Mathlib build-outs, and now known to be **avoidable**.

## Recommended order of execution

1. **Settle the open question:** trace whether `ofCurve_inj` needs R1/R2 or only
   the lattice. (Read-only; decides whether the leaner-lattice refactor is clean.)
2. **Port non-degeneracy** (G1+G2 shared): our `span_real … = ⊤` analog via the
   maximum principle. This is the single highest-leverage lemma.
3. **G4** — torus-self-Albanese (Liouville over the universal cover). The new
   classical theorem; start scoping in parallel.
4. **G3** — wire the existing naturality engine into `AX_period_functoriality`.
5. **Refactor** headlines onto the leaner lattice; retire `AX_PeriodCycleBasis`
   and the three torus axioms. Result: `ofCurve_isJacobian` axiom-clean — the
   `VALIDATION.md` goal — with the whole challenge sorry-free **and** axiom-free,
   by the route Kirov demonstrated is sufficient.
