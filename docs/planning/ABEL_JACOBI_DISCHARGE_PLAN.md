# Abel–Jacobi discharge plan — the project's deepest gap

> ## ✅ The gap described below is CLOSED — 2026-06-07
>
> This 2026-06-04 plan identified the "most serious gap" as the three-axiom
> opacity chain `ofCurve_inj ⟵ AX_ofCurve_inj ⟵ pathIntegralBasepointFunctional
> ⟵ loopIntegralToH1`, where `pathIntegralBasepointFunctional := 0` could hide a
> degeneracy. **All three are now discharged** (2026-06-05): `ofCurve_inj` is a
> theorem (homotopy-invariance / `developingValue` route — *not* the residue
> route this doc anticipated), `pathIntegralBasepointFunctional` is a real `def`
> (the period integral `ω ↦ ∫ ω`), and `loopIntegralToH1` is proved. The
> degeneracy failure mode is closed: `ofCurve` is provably injective in positive
> genus.
>
> **What remains open in the Abel–Jacobi cluster** (see the refreshed per-axiom
> plans for current routes):
> - `AX_AbelTheorem` — the deepest node; crux is the **residue theorem** (route
>   re-vetting in progress). `⊆` still gated on `AX_RiemannRoch` + `AX_SerreDuality`.
> - `pushforwardOneForm` (the trace map) — effort 10; gates `AX_pushforwardOneForm_id`/
>   `_comp`, `AX_pullbackAmbient_preserves_lattice`, `AX_pushforward_pullback`.
> - `AX_ofCurve_contMDiff` — now the most tractable standalone (developing-value route).
> - `AX_pushforwardAmbient_preserves_lattice` — gated on unbuilt `pushforwardH1` / period naturality.
>
> _The 2026-06-04 analysis below is retained for its derivation of why the
> opacity mattered; the "now tractable" section foreshadowed exactly the route
> that landed._

*2026-06-04. Companion to [`AXIOM_AUDIT.md`](../../AXIOM_AUDIT.md), the
[`ofCurve` contract card](../contracts/ofCurve.md), and
[`PHASE_3_INFRA_PLAN.md`](PHASE_3_INFRA_PLAN.md).*

## The gap

Buzzard's challenge is designed so the Jacobian API **cannot** be satisfied by a
hack (`Jacobian := 0`): `ofCurve_inj` forces the Abel–Jacobi map to be genuinely
injective in positive genus. Today that obligation is *assumed*, on top of an
**opaque** functional with no defining equation. The golden report shows
`Jacobian.ofCurve_inj` rests on three opaque axioms:

```
ofCurve_inj  ⟵  AX_ofCurve_inj  (Abel's theorem, curve side)
             ⟵  pathIntegralBasepointFunctional  (OPAQUE — no defining equation)
             ⟵  loopIntegralToH1                  (opaque)
```

The `ofCurve` contract card states it bluntly: this is *"an axiom guarded by an
axiom guarded by an axiom,"* and **cannot be validated on any concrete witness**.
The named failure mode: `pathIntegralBasepointFunctional := 0` makes `ofCurve`
constant — hence *non*-injective — so the opacity is exactly where a degeneracy
could hide. This is **the most serious gap**: more than the Liouville L2/L3
residual (true-but-unproven, no faithfulness risk) and the sheaf-cohomology
cluster (now gated by `SheafCohomologySpec`).

## Why it is now tractable

`pathIntegralBasepointFunctional X P₀ P` is the **period integral**
`ω ↦ ∫_{P₀}^{P} ω`. The real defining equation already exists, half-built, as
`Jacobians.Bridge.kirovBackedFunctional` (in `KirovLineIntegral.lean`):

```lean
kirovBackedFunctional P₀ P : HolomorphicOneForm X →ₗ[ℂ] ℂ
  := fun ω => Vendor.Kirov.lineIntegral (bridgeForm ω) (bridgePath P₀ P)
```

It **shape-matches** the axiom, and its load-bearing inputs are now real:
`bridgePath` (the smooth chart-flat path — discharged this session), Kirov's
`lineIntegral` + `pathSpeed_comp_eq_mfderiv` (vendored, real), `bridgeForm`
(real), and `bridgePath_lineIntegrable` (theorem). The bridgePath keystone was
the prerequisite for exactly this.

Two `sorry`s remain in the way, both FTC-shaped.

## Milestones

### A — the Fundamental Theorem of Calculus (the load-bearing analytic work)

The local-antiderivative property: in the chart at `P`, the derivative of the
period integral w.r.t. the upper endpoint is the 1-form's chart coefficient.

- **A1 — `chartLine_FTC`** (`KirovLineIntegral.lean:614`, `sorry`). FTC for the
  *straight chart-line* from `P` to `(extChartAt P).symm z`:
  ```
  HasDerivAt (fun z => lineIntegral (bridgeForm ω) (chartLine P z))
             (ω.coeff P (φ P)) (φ P)
  ```
  The six reduction lemmas it needs are already present (`extChartAt_chartLine`,
  `pathSpeed_comp_eq_mfderiv`, `mfderiv_extChartAt_self`, …); it is an *assembly*
  + the Mathlib `intervalIntegral` FTC. **Most tractable first step (~days).**
- **A2 — `kirovBackedFunctional_local_antiderivative`** (`KirovLineIntegral.lean:1064`,
  `sorry`). The same FTC for the *full* `bridgePath`. **This is the crux.** A
  2026-06-04 scoping pass (below) found the original docstring route is
  load-bearing on a fact that is **false for the current path definition**, so A2
  needs an explicit route decision before any code lands. Do **not** relabel it
  as a fresh axiom (a prior attempt did; it was reverted — see the docstring).

#### A2 scoping (2026-06-04) — the real obstruction

The intended route was the split
`∫_{P₀}^{φ⁻¹(z)} ω = ∫_{P₀}^{P} ω + ∫_{P}^{φ⁻¹(z)} ω` near `z₀ = φ(P)`, first
term constant, second the chart-line piece (A1). Two facts block it:

1. **`bridgePath` makes an independent `Classical.choice` per endpoint.**
   `bridgePathImpl P₀ Q := (S.concatChartFlatPath).extend` where
   `γ := (exists_path P₀ Q).some` and `S := (exists_pathChartBallSubdivision γ).some`
   — a *fresh* arbitrary path **and** subdivision chosen for each `Q`. So
   `H(z) := ∫_{bridgePath P₀ (φ⁻¹z)} ω` has **no continuity in `z`**: as the
   endpoint moves, the chosen path can jump to a different homotopy class and the
   integral jumps by a **period**. `HasDerivAt H …` (A2's conclusion) requires
   `H` at least continuous — so **A2 is not provable for the current opaque
   `bridgePathImpl`.** The split's "first term constant in `z`" silently assumes
   the `P₀→P` part is reused as `Q` varies; the per-endpoint choice breaks that.

2. **Mathlib's Poincaré lemma lives on `ℂ`, not on the manifold `X`.** The
   path-independence engine we have (next §) deforms contours in `ℂ`; the period
   ambiguity in (1) is a *global* manifold homotopy fact Mathlib does not provide
   for abstract manifolds. So even with chart-local path-independence in hand, the
   global "integral well-defined mod periods" is not free.

The honest content is exactly the **well-definedness-mod-periods** heart of
Abel–Jacobi: the integral is genuinely path-dependent on a positive-genus curve
(that is the whole point — periods are nonzero), and the *derivative* is
well-defined only because the endpoint-variation is chart-local.

#### Path-independence machinery (found in sibling `picard-lefschetz`)

`picard-lefschetz/PicardLefschetz/ContourDeformation.lean` proves contour
deformation = path-independence on `ℂ`, and **all of it is in our Mathlib pin**:

- **Closedness of holomorphic forms** — `holoOneForm_dω_symm`: for ℂ-diff `f`,
  `ω = f(z)dz` has symmetric Fréchet derivative. Proof is
  `HasDerivAt.complexToReal_fderiv` + `ring` (~30 lines, no hard analysis).
- **Mathlib's Poincaré lemma** —
  `curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt`
  (`Mathlib/MeasureTheory/Integral/CurveIntegral/Poincare.lean`, present in our
  pin) consumes that closedness + a homotopy and equates the boundary integrals.
- **Rel-endpoint deformation** — `contourDeformation1D_pathHomotopy_abstract`:
  `∫_{γ₁} ω = ∫_{γ₂} ω` for a `Path.Homotopy` staying in an open `t`.

This resolves the *chart-local* path-independence cleanly (the part previously
feared to be "weeks of from-scratch complex analysis"). It does **not** by itself
close A2 because of obstruction (1)+(2) above.

#### Route fork (HUMAN DECISION — touches the bridgePath keystone or the contract)

- **Route 1 — refine the path's endpoint dependence to a chart-line tail.**
  Restructure so that, near the endpoint, the path is a chart line landing at `Q`,
  and the `P₀→P` core is *reused* as `Q` varies in `chart(P)`. Then
  A2 = A1 + Kirov `lineIntegral_concat`, **no path-independence needed**. Cost:
  touches the just-landed `bridgePath` keystone (re-establish its 5 structural
  properties for the refined construction) — *invasive, keystone risk*. The
  canonical-construction snag: `bridgePath P₀ Q` knows only `P₀,Q`, so a
  "chart-line tail at `Q`" must be intrinsic, not relative to an external `P`.
- **Route 2 — chart-local path-independence (picard-lefschetz port) + a
  manifold homotopy-invariance step.** Keep `bridgePath` opaque; prove the
  endpoint-derivative is path-choice-independent. Needs the picard-lefschetz port
  **plus** a Kirov-`lineIntegral` ↔ Mathlib-`curveIntegral` chart bridge **plus**
  a manifold-level "integral locally constant in endpoint mod periods" lemma
  (the part Mathlib lacks). Additive (no keystone risk) but the manifold step is
  real new work.
- **Route 3 — descope A2.** Bank A1, leave A2/`AX_pathIntegral_local_antiderivative`
  as an honest cited axiom (it is the FTC for Abel–Jacobi, textbook-standard), and
  redirect the push to Milestone C (the `Elliptic` non-degeneracy witness), which
  attacks the *faithfulness* risk directly without the manifold-analysis tail.

**Recommendation:** dispatch the picard-lefschetz port now (the chart-local
path-independence lemma + `holoForm` closedness + Kirov↔curveIntegral bridge) —
it is additive, reusable, low-risk, and is literally the "path independence"
infrastructure. It is a prerequisite for Route 2 and a useful library lemma even
under Route 1/3. **Defer the Route 1-vs-2-vs-3 endpoint decision to the human**
(it touches the keystone or the axiom contract). My lean: Route 3 banks the
faithfulness win (C) fastest; Route 2 is the honest full discharge if the
manifold homotopy step proves tractable on the chart bridge.

### B — discharge the opaque core (mechanical once A lands; −2 axioms)

- `pathIntegralBasepointFunctional X P₀ P := kirovBackedFunctional P₀ P` — replace
  the opaque axiom with the real `def`.
- `AX_pathIntegral_local_antiderivative := kirovBackedFunctional_local_antiderivative`
  — the statements are verbatim-identical once the functional is the Kirov one.

This collapses the "axiom guarded by an axiom": `ofCurve` becomes a **computed**
map, and the FTC link (which the audit notes "prevents the zero-functional from
silently satisfying downstream injectivity") becomes a *theorem*.

### C — validate `ofCurve_inj` against the hack it resists

With `ofCurve` computed, prove `AX_ofCurve_inj` on a **concrete witness**:
`Elliptic ω₁ ω₂` (genus 1), where Abel–Jacobi is essentially the identity
`X → X = ℂ/Λ` and injectivity is checkable. That **pins** `ofCurve` as
non-degenerate on a real curve — the exact validation the contract card says is
currently impossible. Full general Abel's theorem may remain an axiom, but
**witnessed**, not opaque. *(~weeks; the `Elliptic` witness scaffolding —
`aLoop`/`bLoop`/`ellipticCycleBasis` — already exists.)*

## Scope of the next push

**A1 done** (`chartLine_FTC`, commit `9714745`, kernel-verified standard-3). **A2
is gated on the Route 1/2/3 fork above (human decision).** Immediate in-flight
work: the **picard-lefschetz path-independence port** (chart-local: `holoForm`
closedness + Mathlib Poincaré + Kirov↔`curveIntegral` bridge) — additive, safe,
useful under any route. **B** (the `−2` axioms) stays gated on A2; if Route 3 is
chosen, B is deferred and the push pivots to **C** (the `Elliptic` witness),
which attacks the faithfulness risk without the manifold-analysis tail.

Acceptance: `#print axioms ofCurve_inj` no longer lists
`pathIntegralBasepointFunctional` or `AX_pathIntegral_local_antiderivative`; and
(C) `AX_ofCurve_inj` is a theorem for `Elliptic`.

Guardrail (binding, per the contract card): **no relabelling.** A discharge that
re-asserts the FTC under a new axiom name is a regression, not progress — the
analytic content (local path-independence) must be derived.
