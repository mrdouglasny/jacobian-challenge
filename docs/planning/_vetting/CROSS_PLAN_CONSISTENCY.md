# Cross-plan consistency audit — 21 `mathlib-now` plans

**Model:** gemini-3.1-pro-preview  (extended thinking)
**Duration:** 88.7s
**Plans audited:** 21
**Date:** 2026-06-03

This is the cross-plan analysis the per-plan vetting can't do — it catches
Mathlib-decl drift, signature splits, mutual-discharge cycles, and stale
prereqs between plans that each looked fine in isolation. Findings should
be folded back into the per-plan recipes; the cluster cited below is the
authoritative version.

---

## Finding 1 — Divergent complex torus helpers

**Plans involved:** `AX_Elliptic_aLoop_analytic`, `AX_Elliptic_bLoop_analytic`
**Class:** duplicate
**Evidence:** 
Both plans attempt to solve the same atlas-local affine chart behavior in `ComplexTorus.lean` but propose creating different, disjoint lemmas to do it. 

`AX_Elliptic_aLoop_analytic` recommends creating a specific wrapper lemma:
```lean
Mandate adding a public wrapper lemma `extChartAt_eq_sub_lift_lattice_offset` in `Jacobians/AbelianVariety/ComplexTorus.lean`.
```

`AX_Elliptic_bLoop_analytic` instead recommends a generalized shared helper:
```lean
Introduce a general lemma decoupled from the specific `Elliptic` generators:
   private lemma analyticAt_torus_affine_arc {L : AddSubgroup ℂ} [DiscreteTopology L] [Rk2 L]
```
**Recommendation:** Standardize on the generalized `analyticAt_torus_affine_arc` helper proposed by `AX_Elliptic_bLoop_analytic` and have both A-cycle and B-cycle proofs invoke it.

## Finding 2 — Line bundle representation mismatch

**Plans involved:** `LineBundle`, `H1`
**Class:** signature
**Evidence:** 
`LineBundle` explicitly defines the bundle as a trivial phantom type without any internal fields:
```lean
def LineBundle {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (D : Divisor X) : Type := PUnit
```

However, `H1` (and similarly `H0-instModule`) attempts to project a `.sheaf` field out of this type, which will fail to compile against `PUnit`:
```lean
def H1 {X : Type*} [...] {D : Divisor X} (L : LineBundle D) : Type :=
  (L.sheaf).H 1
```
**Recommendation:** Resolve the API split: either upgrade `LineBundle` to return a structure containing the locally-free sheaf (abandoning the `PUnit` token design), or refactor `H1` (and `H0`) to construct the sheaf locally from the divisor `D` without calling a `.sheaf` projection on `L`.

## Finding 3 — Divisor mutual dependency loop

**Plans involved:** `Divisor`, `Divisor-instAddCommGroup`
**Class:** mutual-no-anchor
**Evidence:** 
`Divisor` claims to be blocked by the instance:
```text
Blocked by: `Divisor.instAddCommGroup` (`Jacobians/RiemannSurface/LineBundle.lean:56`)
```

`Divisor-instAddCommGroup` conversely claims to be blocked by the underlying type definition:
```text
Blocked by: `Divisor` (`Jacobians/RiemannSurface/LineBundle.lean:51`)
```
**Recommendation:** Break the circular dependency chain by removing `Divisor.instAddCommGroup` from the `Blocked by` list of `Divisor`. The `abbrev` definition is the true anchor.

## Finding 4 — Dropped instance binders in Divisor instances

**Plans involved:** `Divisor`, `Divisor-instAddCommGroup`
**Class:** signature
**Evidence:** 
`Divisor` demands 6 implicit manifold/topology instance binders for the type `X` to be well-formed:
```lean
abbrev Divisor (X : Type u) [_ : TopologicalSpace X] [_ : T2Space X]
    [_ : CompactSpace X] [_ : ConnectedSpace X] [_ : ChartedSpace ℂ X]
    [_ : IsManifold 𝓘(ℂ) ω X] : Type u := FreeAbelianGroup X
```

But `Divisor-instAddCommGroup` intentionally strips them out to simplify the typeclass context:
```lean
instance Divisor.instAddCommGroup {X : Type*} : AddCommGroup (Divisor X) :=
  inferInstanceAs (AddCommGroup (FreeAbelianGroup X))
```
This creates a signature incompatibility: Lean will fail to elaborate the `(Divisor X)` return type in the instance declaration because the required typeclasses for `X` are absent from the context.
**Recommendation:** Retain the full set of topological and manifold instance binders in the signature of `Divisor-instAddCommGroup`.

## Finding 5 — Stale circularity expectation for chart transitions

**Plans involved:** `affineLiftChart_compat_infinityLiftChart`, `infinityLiftChart_compat_affineLiftChart`
**Class:** stale
**Evidence:** 
`affineLiftChart_compat_infinityLiftChart` lists the symmetric chart transition as a blocker, relying on it to supply a derivative shortcut:
```text
Blocked by: `infinityLiftChart_compat_affineLiftChart` (the symmetric direction; the two recipes share the same case-split skeleton and one supplies the chart-transition-derivative input to the other via `Jacobians.GeneralResults.transition_fderiv_mul`)
```

However, `infinityLiftChart_compat_affineLiftChart` has since been rewritten to explicitly reject this approach:
```text
Removed Route B (Mathematical Circularity): Completely scrapped the previous Route (B) which erroneously proposed using the Inverse Function Theorem and `transition_fderiv_mul`.
```
**Recommendation:** Remove `infinityLiftChart_compat_affineLiftChart` from the `Blocked by` list of `affineLiftChart_compat_infinityLiftChart` and delete the expected shortcut via `transition_fderiv_mul`; both transition directions must now be discharged independently via explicit 4-case algebraic proofs.

CROSS-PLAN VERDICT: 5 findings (5 actionable) — Identified one duplicated helper lemma, a fatal signature mismatch breaking line bundle sheaf cohomology, a blocked-by loop, a dropped-binder error in an instance, and a stale expectation regarding chart transition derivatives.
