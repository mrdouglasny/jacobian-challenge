# Discharging `AX_ofCurve_inj` — Abel injectivity (Elliptic witness → general)

*2026-06-05. The anti-degeneracy heart of Buzzard's challenge: `ofCurve` must be
genuinely injective in positive genus. Companion to
[`ABEL_JACOBI_DISCHARGE_PLAN.md`](ABEL_JACOBI_DISCHARGE_PLAN.md).*

## The target

```lean
-- Axioms/AbelJacobiMap.lean
axiom AX_ofCurve_inj (P : X) (_h : 0 < genus X) : Function.Injective (ofCurveImpl X P)
```
This is **the** anti-hack obligation. `ofCurveImpl P Q := [ (∫_P^Q ω_i)_i ] ∈ Jacobian X`
(now a real computed map, post the `loopIntegralToH1` discharge). Goal: replace the
axiom with a **theorem**, validated concretely on `Elliptic` first, then general.

## Assets in hand
- `AX_AbelTheorem` (`Axioms/AbelTheorem.lean`, Class-1 textbook): `ker (abelJacobiDiv X) = PrincipalDivisors X`.
- `abelJacobiDiv : Divisor X →+ Jacobian X` (extends `ofCurveImpl` to divisors).
- `Extensions/AbelJacobi.lean`: partial `ofCurveImpl`↔`abelJacobiDiv`↔Abel machinery
  (`abelJacobi_hyperellipticInvolution`, `abelJacobi_fiber_sum_eq_zero` — has `sorry`s).
- `Elliptic ω₁ ω₂ h := ℂ ⧸ Λ` (`ellipticLattice`); `ellipticDz` (the form `dz`, `coeff = 1`);
  `ellipticCycleBasis`; the L0–L1 multi-chart integral (`canonicalArcIntegral`).

## Milestone E — the Elliptic witness (FIRST, concrete)

Prove `Function.Injective (ofCurveImpl (Elliptic ω₁ ω₂ h) P)` directly.

- **E1** `ofCurveAmbient (Elliptic) P₀ P = (lift P − lift P₀)` in `ℂ` (mod `Λ` after quotient):
  `ofCurveAmbient P₀ P i = ∫_{P₀}^{P} (jacobianBasis i)`, and the genus-1 basis form is a
  scalar multiple of `ellipticDz` (`coeff = 1`), so the line integral `∫ dz =` endpoint
  difference in the chart. Uses the L0–L1 integral + `kirovBackedFunctional` unfolding on
  `ℂ/Λ`. *The analytic core of the witness.*
- **E2** `ofCurveImpl (Elliptic) P = (fun Q => [Q − P])`, a **translation** on `ℂ/Λ`;
  translations are injective ⇒ `ofCurve_inj` for `Elliptic`. *(Mechanical given E1.)*

Validates `ofCurve` as non-degenerate on a real curve — exactly the contract-card
obligation that was "currently impossible".

## Milestone G — the general theorem (`AX_ofCurve_inj` for all `genus > 0`)

Derive from `AX_AbelTheorem` (keep Abel as the textbook axiom; trade `AX_ofCurve_inj`
for a derivation):

- **G1** point↔divisor bridge: `ofCurveImpl P Q = abelJacobiDiv ((Q : Divisor) − (P))`
  (from the `AddMonoidHom`-extension property of `abelJacobiDiv`). Finish the related
  `sorry`s in `Extensions/AbelJacobi.lean` as a by-product.
- **G2** `AX_AbelTheorem`: kernel = principal divisors (existing axiom).
- **G3 (crux)** `genus > 0 ⇒ ∀ Q₁ Q₂, (Q₁) − (Q₂) ∈ PrincipalDivisors → Q₁ = Q₂`.
  Classical: a single-zero/single-pole function is a degree-1 map to ℙ¹ ⇒ genus 0. The
  honest source is **`AX_RiemannRoch`** (`h⁰((Q₂)) = 1` for `genus > 0`, only constants),
  or a dedicated lemma. Likely the one remaining hard analytic/algebraic step.
- **Assembly**: `ofCurve P Q₁ = ofCurve P Q₂` ⇒ `abelJacobiDiv((Q₁)−(Q₂)) = 0` (G1) ⇒
  `(Q₁)−(Q₂)` principal (G2) ⇒ `Q₁ = Q₂` (G3).

## Sequencing
**E1 → E2** (the concrete witness, leverages the just-built integral machinery), then
**G1 → G3 → assembly** (the general theorem). G3 is the genuine difficulty (it pulls in
Riemann–Roch); E's genus-1 instance of G3 is the classical elliptic Liouville fact
(provable in-repo).

Guardrail: no relabelling — `AX_ofCurve_inj` must become a *derived* theorem, and the
Elliptic witness must be a genuine computation (not `ofCurve := id` dressed up). Review
against `DEFINITIONS_AUDIT.md` before merge.

## Unification (2026-06-05) — drop Kirov's lineIntegral, put ofCurve + periods on one integral

Root cause of the E2/G1 block: `ofCurve` uses `kirovBackedFunctional` (Kirov `lineIntegral`
over `bridgePath`) while the period lattice uses `canonicalArcIntegral` (the L0–L1 integral over
analytic arcs) — two integrals, never reconciled. KEY: `bridgePath` is **piecewise-analytic**
(built from `chartFlatPath` = `flatSegment` affine segments, analytic in charts), so it CAN be
an `AnalyticArc` and `canonicalArcIntegral` applies. Unify on `canonicalArcIntegral`:

- **U1** `bridgePathArc P₀ P : AnalyticArc X` — give `bridgePath` an `AnalyticArc` structure
  (partition = subdivision breakpoints `S.breakpoints`; `is_analytic` on each gap from
  `chartFlatPath` = flat affine in `S.chart n` + analytic chart-transition; infra
  `chartFlatPath_chart_eventuallyEq_flatSegment` exists). *Foundational.*
- **U2** re-base `pathIntegralBasepointFunctional := canonicalArcIntegral (bridgePathArc P₀ P)`
  (replace `kirovBackedFunctional`).
- **U3** `canonicalArcIntegral` concat/reverse API (Kirov had these; needed for the G1 cocycle).
- **U4** retire `Kirov.lineIntegral` / `kirovBackedFunctional` usage in `ofCurve`. KEEP Kirov's
  Montel finite-dimensionality + `bridgeForm` (they drive `FiniteDimOneForms`, separate).

Result: `ofCurve` and the period lattice use ONE integral ⇒ the G1 cocycle, ofCurve-loops-∈-lattice,
and (deferred) homotopy invariance all live in one framework. Then E2/G1 unblock; homotopy
invariance becomes the single remaining analytic prerequisite for full path-independence.
