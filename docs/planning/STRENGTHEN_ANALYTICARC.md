# Strengthening `IsAnalyticArc` (decoupled-`f` form)

*2026-06-06. MRD-approved. Gemini-deep-think-vetted design. Branch
`strengthen-analyticarc`. Goal: make the per-cell regularity strong enough that
interval-integrability of the period integrand is a free corollary — which
**retires `AX_cycleBasisLoop_integrable`** (60 → 59 axioms) and discharges the
two integrability hypotheses carried by the HI-0 bridge (PR #76).*

## Why the current predicate is too weak

```
IsAnalyticArc := ∀ u ∈ Ioo 0 1, u ∉ partition →
    AnalyticAt ℝ (fun r => extChartAt 𝓘(ℂ) (extend u) (extend r)) u
```

Pointwise-analytic on the **open** interior, in the **moving** chart centred at
`extend u`. This admits arcs of shape `r²sin(1/r²)`: analytic at every interior
point but with derivative unbounded approaching the cell endpoint, hence the
period integrand is **not** `IntervalIntegrable` up to the closed-cell endpoints.
So the bridge theorem is forced to *carry* `hfixed_integrable` / `hcanonical_integrable`
as undischargeable hypotheses, and `AX_cycleBasisLoop_integrable` exists purely to
paper over this (its own docstring: *"can be retired by strengthening AnalyticArc"*).

## The vetted strong predicate (decoupled `f`)

Gemini caught a critical flaw in the naive fix: requiring
`AnalyticOn (extChartAt p ∘ extend) U` on an **open** `U ⊇ Icc s t` is
**impossible at a concatenation site** — `U` must poke past the ½-junction where
the global `extend` turns a corner, so the composite is not analytic there.

**Fix — decouple the analytic witness `f` from the global `extend`:** demand an
analytic `f` on `U` that coincides with the chart-composite only on the **closed**
cell. `f` analytically continues the *left* piece's trajectory past the junction;
the corner of `extend` is irrelevant because we never ask `extend` itself to be
analytic past the cell.

```lean
def IsAnalyticArcStrong (X) [...] (extend : ℝ → X) (partition : Finset ℝ) : Prop :=
  ∀ s ∈ partition, ∀ t ∈ partition, s < t →
    (∀ r ∈ partition, r ∉ Set.Ioo s t) →            -- s,t consecutive
    ∃ (p : X) (U : Set ℝ) (f : ℝ → ℂ),
      IsOpen U ∧ Set.Icc s t ⊆ U ∧ AnalyticOn ℝ f U ∧
      (∀ r ∈ Set.Icc s t, extend r ∈ (extChartAt 𝓘(ℂ) p).source) ∧
      (∀ r ∈ Set.Icc s t, extChartAt 𝓘(ℂ) p (extend r) = f r)
```

Keep `AnalyticOn ℝ f U` with an **explicit open `U`** (not `AnalyticOnNhd` on
`Icc`): the explicit open set avoids reasoning about `extChartAt`'s junk values
outside its source, and makes `AnalyticOn → ContDiffOn → continuousOn_deriv` clean.

## Verdicts (Gemini deep-think, 2026-06-06)

- **(a) Sufficient for `IntervalIntegrable(canonicalIntegrand) on [0,1]`.** Per
  cell: the fixed-centre integrand `Fp_f(r) = form.coeff p (f r) · deriv f r` is
  continuous on the compact `Icc s t` (`AnalyticOn.contDiffOn` →
  `ContDiffOn.continuousOn_deriv` → `·` continuous holomorphic coeff), hence
  `ContinuousOn.integrableOn_Icc → IntervalIntegrable`. On `Ioo s t` it equals
  `canonicalIntegrand` (moving=fixed integrand-independence, already proven;
  `deriv extend = deriv f` since they agree on a nbhd in the interior). `Ioo`
  vs `Ioc` differ by measure zero → `IntegrableOn.congr_fun_ae`. Sum the finitely
  many cells with `IntervalIntegrable.trans`. **No gap at partition points** —
  the corner value of `deriv extend` is a measure-zero set the Lebesgue integral
  ignores.
- **(b) Implies the weak form.** For interior `u`, near `u` the cell coincidence
  gives `extChartAt(extend u)(extend r) = (transition)(f r)` with
  `transition = extChartAt(extend u) ∘ (extChartAt p).symm` complex-analytic
  (manifold) → real-analytic via `AnalyticAt.restrictScalars`; then
  `AnalyticAt.comp`. The linchpin lemma already exists:
  `Jacobians.Bridge.extChartAt_trans_analyticAt` (BridgePathArc.lean:22).
- **(c) Use `AnalyticOn ℝ f U`, explicit open `U`.** (above)

## Minimal-ripple implementation

1. **Structure field** `is_analytic_strong : IsAnalyticArcStrong X extend partition`
   replaces the old weak field.
2. **Derived lemma `AnalyticArc.is_analytic`** reproduces the *old* weak signature
   `∀ u ∈ Ioo 0 1, u ∉ partition → AnalyticAt ℝ (...moving...) u` from
   `is_analytic_strong` (via the transition linchpin). **Named `is_analytic`** so
   the 4 consumer call-sites (`γ.is_analytic u h h` in `OfCurveInj`,
   `ArcChartDifferentiable`, two in `ArcAlgebra`) are **untouched** — `is_analytic`
   becomes a lemma with the same application shape as the former field.
3. **6 constructors** supply the strong field instead of the weak one:
   - `Elliptic/Witnesses` `AX_Elliptic_{a,b}Loop_analytic` — statements strengthen
     to `IsAnalyticArcStrong`; the affine-in-chart justification (`fderiv = 1` ⇒
     locally affine ⇒ entire ⇒ analytic on any nbhd) supports the strong form.
     Re-vet, mark `(NOT VERIFIED)` until re-checked. (Count unchanged: still 2 axioms.)
   - `Line/Witnesses` analogues.
   - `BridgePathArc` — `f` from `analyticAt_flatSegment`/the flat reparam.
   - `ArcAlgebra.reverse`/`trans` — propagate `(p, U, f)` through `t↦1−t` and the
     ½-split; the decoupling makes `trans` tractable (each piece keeps its own `f`).
4. **Integrability lemma** `analyticArc_canonicalIntegrand_intervalIntegrable`
   from `is_analytic_strong` (sketch (a)).
5. **Retire `AX_cycleBasisLoop_integrable`** → `theorem` from (4). Delete the axiom.
6. **Discharge #76** `hfixed_integrable`/`hcanonical_integrable` from (4).
7. Rebuild `Jacobians`, regen `docs/axiom-report.txt`, set all counts to **59**
   (the new CI consistency guard enforces agreement), update `AXIOM_AUDIT.md`.

## Guardrails
No new axiom (net −1). Build-gate each checkpoint with `lake env lean` / `lake build`.
`#print axioms` on the retired-axiom theorem + the headlines (no `sorryAx`, no
`AX_cycleBasisLoop_integrable`). Re-vet the strengthened witness axioms before
relying on them.
