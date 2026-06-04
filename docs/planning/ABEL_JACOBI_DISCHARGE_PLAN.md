# Abel–Jacobi discharge plan — the project's deepest gap

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
- **A2 — `kirovBackedFunctional_local_antiderivative`** (`:695`, `sorry`). The
  same FTC for the *full* `bridgePath`. The honest route (per its docstring): the
  z-derivative is **local** — `∫_{P₀}^{φ⁻¹(z)} ω = ∫_{P₀}^{P} ω + ∫_{P}^{φ⁻¹(z)} ω`
  near `z₀`, the first term constant in `z` (derivative 0), the second the
  chart-line piece (A1). The real content is **local path-independence** of the
  holomorphic 1-form integral (the integrand is a local exact differential — the
  cocycle content of `HolomorphicOneForm`). *This is the crux (~weeks of complex
  analysis).* Do **not** relabel it as a fresh axiom (a prior attempt did; it was
  reverted — see the docstring).

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

**A1 → A2 → B.** Landing these converts the deepest opaque axiom into a real
computed functional with a proven FTC, eliminating the "axiom guarded by an
axiom" and removing 2 axioms (the opaque functional + the FTC axiom). **C** is
the follow-on that validates the anti-hack obligation on a concrete curve.

Acceptance: `#print axioms ofCurve_inj` no longer lists
`pathIntegralBasepointFunctional` or `AX_pathIntegral_local_antiderivative`; and
(C) `AX_ofCurve_inj` is a theorem for `Elliptic`.

Guardrail (binding, per the contract card): **no relabelling.** A discharge that
re-asserts the FTC under a new axiom name is a regression, not progress — the
analytic content (local path-independence) must be derived.
