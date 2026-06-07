# Challenge axiom map — per-obligation axiom requirements

*Regenerable from `docs/axiom-report.txt` (the kernel-checked golden report) +
`#print axioms Jacobians.ofCurve_isJacobian`. Last computed 2026-06-07 against the
50-axiom kernel.*

This maps **what each piece of the challenge actually rests on**, in three tiers:

1. **Buzzard's 24 sorries** (`Jacobians/Challenge.lean`) — the API he requires.
2. **The Albanese universal property** (`ofCurve_isJacobian`) — our enrichment.
3. **Foundational material** (RR / Serre / sheaf cohomology) — judged by
   *definitional faithfulness*, not proof status (per the discussion below).

Notation: the **torus core** `{AX_AnalyticCycleBasis, intersectionForm}` (+ for
manifold/holomorphic structure `{AX_PeriodLattice, instPeriodLatticeDiscrete}`)
underlies almost everything — the Jacobian *is* a period torus. Per-row axioms
below are the **project axioms beyond propext/choice/Quot**; `(torus core)` is
abbreviated where it recurs.

---

## Tier 1 — Buzzard's 24 sorries

Classification (from `docs/challenge-annotated.md`): **F** = data/definition,
**H** = hybrid, **T** = property/theorem. "Status" is current.

### Data sorries (§1–§13)

| § | Obligation | Class | Status | Required project axioms |
|---|------------|-------|--------|--------------------------|
| 1 | `def genus` | F | ✓ real def | **none** (axiom-free) — but rests on the `HolomorphicOneForm` carrier; its faithfulness is a live definitional question (see Tier 3) |
| 2 | `def Jacobian` (type) | F | ✓ real def | `AX_AnalyticCycleBasis`, `intersectionForm` |
| 3 | `AddCommGroup` | F | ✓ instance | (inherits §2) |
| 4 | `TopologicalSpace` | F | ✓ instance | (inherits §2) |
| 5 | `T2Space` | H | ✓ instance | + `instPeriodLatticeDiscrete` |
| 6 | `CompactSpace` | H | ✓ instance | + `AX_PeriodLattice` (full-rank ⇒ compact) |
| 7 | `ChartedSpace` | F | ✓ instance | (inherits §2; complex structure axiom-free) |
| 8 | `IsManifold` | H | ✓ instance | (inherits) |
| 9 | `LieAddGroup` | H | ✓ instance | (inherits) |
| 10 | `def ofCurve` | F | ✓ real def | `AX_AnalyticCycleBasis`, `intersectionForm` |
| 11 | `def ContMDiff.degree` | F | ✓ real def | **none** (`AX_BranchLocus` is now a theorem) |
| 12 | `def pushforward` | F | ✓ real def | (torus core), `AX_pushforwardAmbient_preserves_lattice` |
| 13 | `def pullback` | F | ✓ real def | (torus core), `AX_pullbackAmbient_preserves_lattice`, **`pushforwardOneForm`** (the trace) |

**Foundation = fully built:** every F/H sorry is a real `def`/`instance`; no
axiom-routed *foundation* remains at the Buzzard interface. The only data-level
axioms are the *period-torus structure* (`AX_AnalyticCycleBasis`, `intersectionForm`,
`AX_PeriodLattice`, `instPeriodLatticeDiscrete`) and the *trace* `pushforwardOneForm`
(used by pullback).

### Theorem sorries (§14–§24)

| § | Obligation | Status | Required project axioms (beyond torus core) |
|---|------------|--------|----------------------------------------------|
| 14 | `genus_eq_zero_iff_homeo` | axiom-routed | `AX_genus_eq_zero_iff_homeo` |
| 15 | `ofCurve_contMDiff` | axiom-routed | `AX_ofCurve_contMDiff` *(now most tractable — developing-value route)* |
| 16 | `ofCurve_self` | ✓ derived thm | none (definitional) |
| 17 | `ofCurve_inj` | ✓ derived thm | **`AX_AbelTheorem`** — uses the **⊆ (hard) direction** |
| 18 | `pushforward_contMDiff` | ✓ derived thm (PR #88) | `AX_pushforwardAmbient_preserves_lattice` |
| 19 | `pushforward_id_apply` | ✓ derived thm | `AX_pushforwardAmbient_preserves_lattice` |
| 20 | `pushforward_comp_apply` | ✓ derived thm | `AX_pushforwardAmbient_preserves_lattice` |
| 21 | `pullback_contMDiff` | ✓ derived thm (PR #88) | `AX_pullbackAmbient_preserves_lattice`, `pushforwardOneForm` |
| 22 | `pullback_id_apply` | ✓ derived thm | `AX_pullbackAmbient_preserves_lattice`, `AX_pushforwardOneForm_id`, `pushforwardOneForm` |
| 23 | `pullback_comp_apply` | ✓ derived thm | `AX_pullbackAmbient_preserves_lattice`, `AX_pushforwardOneForm_comp`, `pushforwardOneForm` |
| 24 | `pushforward_pullback` | axiom-routed | `AX_pushforward_pullback`, both `*Ambient_preserves_lattice`, `pushforwardOneForm` |

### Tier-1 distinct axioms (the challenge core) — **13**

`AX_AnalyticCycleBasis`, `intersectionForm`, `AX_PeriodLattice`,
`instPeriodLatticeDiscrete` (torus structure) · `AX_genus_eq_zero_iff_homeo` ·
`AX_ofCurve_contMDiff` · `AX_AbelTheorem` (⊆ only) · `pushforwardOneForm` ·
`AX_pushforwardOneForm_id` · `AX_pushforwardOneForm_comp` ·
`AX_pushforwardAmbient_preserves_lattice` · `AX_pullbackAmbient_preserves_lattice` ·
`AX_pushforward_pullback`.

These 13 are the *entire* axiomatic content of solving Buzzard's challenge.

---

## Tier 2 — Albanese universal property

`ofCurve_isJacobian` (`UniversalProperty.lean:457`): the concrete `Jacobian X`
*is* the Jacobian (Albanese universal property — every holomorphic map to a torus
factors uniquely through `ofCurve`). **Not a Buzzard obligation** — our enrichment.

`#print axioms` closure (2026-06-07):
> (torus core) + `AX_ofCurve_contMDiff` + **`AX_curve_generates_jacobian`** +
> **`AX_period_functoriality`** + **`AX_torus_oneforms_dualCover`** +
> **`AX_torus_self_albanese`**.

**Tier-2 adds exactly 4 axioms** over the challenge core — the **Albanese
cluster** (bolded). Everything else it needs is shared with Tier 1. So the
universal property is a *cheap enrichment in axiom terms* (4 torus/Albanese
axioms), independent of the RR/Serre foundational tier.

---

## Tier 3 — Foundational material (RR / Serre / sheaf cohomology)

**Different status, per the right question.** These are **not** consumed by Tier 1
or Tier 2 (they appear in *zero* challenge/universality closures). For this tier
the question is **"is it properly *defined*?"** — a faithful statement that
type-checks against real objects — far more than "is it *proven*?". A faithful,
sorry-ed statement is the real deliverable; the proof is deferred classical work.

| Object | Kind | Definitional status | Proof status |
|--------|------|---------------------|--------------|
| `riemannRochSpace` (`L(D)`) | def | ✓ **faithful** — a ℂ-submodule of the meromorphic germ quotient `MeroField = MeroFunctions ⧸ GermZero` (corrected from a degenerate raw-`X→ℂ` version that admitted "spike" functions; `germZero_ne_bot` witnesses the old bug) | `h0_zero` (`h⁰(0)=1`) **proven** axiom-free |
| `LineBundle`, `LineBundle.ofDivisor` | axiom (type/data) | ⚠ **stub** — sheaf-cohomology placeholder type; faithfulness gated by `SheafCohomologySpec` | n/a |
| `H1`, `H1.instAddCommGroup`, `H1.instModule` | axiom (type/data) | ⚠ **stub** — `H¹` placeholder; gated by `SheafCohomologySpec` | n/a |
| `canonicalDivisor` | axiom (data) | ⚠ **stub** — class-2a | n/a |
| `AX_RiemannRoch` | axiom (Prop) | statement scaffolded in `RiemannRochAPI` (**8 sorries** — RR identity, `h⁰(K)=g`, finite-dim `L(D)`) | deep; needs sheaf-cohomology LES + Serre finiteness |
| `AX_SerreDuality` | axiom (Prop) | statement scaffolded in `SerreDualityAPI` (**2 sorries**) | deep |
| `AX_PluckerFormula` | axiom (Prop) | `PluckerAPI` statements **fully proved** (reduce to the formula axiom) | formula axiom + plane-curve atlas |
| `AX_IntersectionForm_alternating`, `_perfect` | axiom (Prop) | the intersection-pairing *properties* (Poincaré duality / alternating) — the Hodge/bilinear-relations facet; pairing *data* `intersectionForm` is in Tier 1, its *properties* are here | deep |

**Reading:** for Tier 3 the live work is **faithful definitions + faithful
statements** (the `SheafCohomologySpec` suite, the corrected `MeroField` `L(D)`,
the `*API` sorry-ed statements), not proofs. A degenerate definition passes CI
just like a faithful one, so *definitional faithfulness is where the risk lives*
(cf. the corrected `riemannRochSpace`). These axioms re-enter the *challenge*
critical path only if `AX_AbelTheorem`'s ⊆ is discharged via the **Forster**
route (which consumes RR+Serre); the **Mumford theta** route keeps them out
(Discussion #100).

---

## Concrete-curve witnesses (a fourth, separate category)

The remaining ~21 axioms (Hyperelliptic atlas cluster, `PlaneCurve` instances,
`AX_Hyperelliptic_genus`, `AX_Elliptic_H1_symplectic`, `AX_H1_ProjectiveLine_trivial`,
`AX_PlaneCurveAffine_*`, the IFT lemma) are **not** in any abstract obligation
closure — the obligations are universally quantified over an arbitrary `X`. But
they are the **anti-vacuity witnesses**: evidence that real curves (ℙ¹, elliptic,
hyperelliptic, plane) satisfy the hypotheses and that `genus` computes correctly
on them. Not droppable in spirit — they are the validation layer, not enrichment.

---

## Summary

| Tier | What | Distinct axioms |
|------|------|-----------------|
| 1 | Buzzard's 24 sorries (the challenge) | **13** |
| 2 | Albanese universal property | +4 (Albanese cluster) |
| 3 | RR / Serre / sheaf cohomology | foundational — judged by *definitional faithfulness*; **not** on the Tier-1/2 path (unless Abel ⊆ goes via Forster) |
| — | Concrete-curve witnesses | ~21 — anti-vacuity validation, not abstract obligations |

**Regenerate:** `lake env lean scripts/axiom_report.lean > docs/axiom-report.txt`
for Tier 1/2 closures; `#print axioms Jacobians.ofCurve_isJacobian` for Tier 2.
