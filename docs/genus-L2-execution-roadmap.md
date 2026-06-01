# Liouville L2 — execution roadmap

*Authored 2026-06-01.* Concrete, lemma-by-lemma plan for proving
`AX_HyperellipticForm_polynomial_decomposition` (Liouville L2), the last hard
gap toward a fully axiom-clean even-genus theorem. Companion to the scoping
doc [`genus-L2-L3-discharge-plan.md`](genus-L2-L3-discharge-plan.md); this one
is the *how*, with signatures and an order to execute against.

## Strategy decision: elementary chart-gluing (no involution)

The classical proof writes `R := ω/(dx/y)`, observes `R` is σ-invariant (so
`R ∈ ℂ(x)`) via the hyperelliptic involution `σ(x,y)=(x,−y)`, then bounds it.
**The even side has no `σ` built** (only the odd side does), and proving
"holomorphic differentials are σ-anti-invariant" is itself deep (it needs
`H⁰(Ω)` of the `ℙ¹` quotient `= 0`).

**We avoid `σ` entirely.** The candidate `G := coeff_ω · √f` is built
chart-locally and glued using the **now-real cocycle** (task #21):
- along each sheet, by the same-summand cocycle (identity transition);
- *across* branch points (`y=0`), by the projY chart — this is where the two
  sheets connect, so single-valuedness emerges *from* the branch-point
  analysis, not from `σ`;
- at infinity, by the cross-summand cocycle.
Branch points become **removable singularities** (Mathlib:
`Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`,
`differentiableOn_update_limUnder_of_bddAbove`). More laborious than the `σ`
route, but elementary and built on what we already have.

## Target (restated)

```lean
theorem hyperellipticForm_polynomial_decomposition
    {H : HyperellipticData} [Fact (¬ Odd H.f.natDegree)]
    (form : HolomorphicOneForm (HyperellipticEvenProj H)) :
    ∃ g : Polynomial ℂ, g.natDegree < H.f.natDegree / 2 - 1 ∧
      ∀ a (hpY : a ∈ smoothLocusY H) q (hQ : Quotient.out q = Sum.inl a) {z}
        (hz : z ∈ (affineChartProjX a hpY).target),
        form.coeff q z = g.eval z / (squareLocalHomeomorph a hpY).symm (H.f.eval z)
```

## Milestones

### M0 — Foundations / de-risk (~3–5 days)
- **M0.1** `branch_sqrt_analytic`: `z ↦ (squareLocalHomeomorph a hpY).symm (H.f.eval z)`
  is `AnalyticOn` the projX target. *(Composition of the IFT branch with a
  polynomial; likely already inside `affineProjXCoeff`'s analyticity proof —
  reuse.)*
- **M0.2** `coeff_analytic`: `form.coeff q` is `AnalyticOn (extChartAt q).target`
  (this is `form.2.1`, `IsHolomorphicOneFormCoeff`). Confirm the projX target
  equals the EvenProj chart target at `q` (out = inl a, smooth-Y).
- **M0.3** **Design the global `G`.** Decide its domain: a function
  `G : ℂ → ℂ` on the `x`-coordinate, with `G z := form.coeff q z · √f(z)` for
  `z` in a smooth-Y projX target. Pin down how the two sheets over the same
  `z` are reconciled (they must give the same `G z` — proven in M2 via the
  branch-point bridge). *This is the main design decision; get it right before
  M1.*

### M1 — `G` analytic off the branch locus (L2-a + L2-b, ~1 week)
- **M1.1** `G` well-defined on `{z | f(z) ≠ 0}`: two smooth-Y projX charts over
  the same `z`, same sheet → same-summand cocycle (identity transition) gives
  equal `coeff`, equal `√f`, equal `G`. *(The same-summand cocycle
  `hyperellipticEvenCoeff_cocycle_inl_inl` is real; mirror its use.)*
- **M1.2** `G` analytic on `{z | f(z) ≠ 0}` (product of M0.1 × M0.2).
- *Open:* the two-sheet reconciliation (same `z`, different sheet) is deferred
  to M2 (the sheets only meet at branch points).

### M2 — branch points are removable (L2-c, ~1–2 weeks, **hard**)
- **M2.1** Near a branch point `x₀` (`f(x₀)=0`), use the projY chart at the
  corresponding curve point + the same-summand cocycle to express `G` and show
  it is **bounded** as `z → x₀`. The projX coeff blows up like `1/√f`, the
  cocycle's transition derivative supplies the canceling `√f` factor — the net
  `G` stays bounded. *(This is the crux: the cocycle bookkeeping at `y=0`.)*
- **M2.2** `G` extends analytically across each branch point:
  `analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt` from M1.2 +
  M2.1. The branch locus `{f=0}` is finite (squarefree `f`).
- **M2.3** ⇒ `G` is **entire** on `ℂ` (M1.2 ∪ M2.2, finite branch set), and
  single-valued (the projY chart at `x₀` sees both sheets, forcing them equal).

### M3 — polynomial growth at infinity (L2-d, ~1–2 weeks, **hard**)
- **M3.1** Pull `form.coeff` to the affine-infinity chart (coordinate `u=1/x`)
  via the **cross-summand cocycle** (`hyperellipticEvenCoeff_cocycle_inl_inr`,
  real). Its analyticity at `u=0` bounds the growth of `G(z)` as `|z|→∞`.
- **M3.2** `growth_bound`: `∃ C, ∀ z, ‖G z‖ ≤ C · (1+‖z‖)^(N/2−2)`. The exponent
  `N/2−2` comes from the `u^{g−1}` factor in `infReverse` / the Möbius change
  of variable.

### M4 — assemble (L2-e + packaging, ~3–5 days)
- **M4.1** `G` entire (M2.3) + polynomial growth (M3.2) ⇒ `∃ g, g.natDegree ≤
  N/2−2 ∧ ∀ z, G z = g.eval z`, by
  `differentiable_eq_polynomial_of_growth` (**already proven**).
- **M4.2** `g.natDegree < N/2−1` (from `≤ N/2−2`).
- **M4.3** Unwind: for any smooth-Y projX chart, `form.coeff q z = G z / √f(z)
  = g.eval z / √f(z)` (M0.3 definition + M4.1). Package as the target theorem;
  replace the L2 axiom.

## Then: L3 and the genus theorem
With L2 a theorem, **L3** follows by the propagation argument
([`genus-L2-L3-discharge-plan.md`](genus-L2-L3-discharge-plan.md) §propagation)
using the bridge lemma `hyperellipticForm_coeff_projX` (already proven) — or
do the propagation first as an independent, tractable chunk that collapses
L3 into L2. Then `genus_HyperellipticEven_le` is axiom-clean.

## Dependencies & tools (all confirmed present)
- Real cocycle theorems (task #21): `hyperellipticEvenCoeff_cocycle_{inl_inl,inl_inr,inr_inl,inr_inr}`.
- `differentiable_eq_polynomial_of_growth` (`GeneralResults/EntireGrowth.lean`).
- Mathlib removable singularity: `Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`, `…differentiableOn_update_limUnder_of_bddAbove`.
- Mathlib identity theorem: `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`.
- Chart infra: `affineChartProjX`, `affineChartProjY`, `squareLocalHomeomorph`, `polynomialLocalHomeomorph`, `smoothLocusY/X`.

## Risk register
- **M2.1 (branch-point boundedness)** — highest risk. The cocycle derivative
  factor at `y=0` must exactly cancel the `1/√f` blow-up; this is a real
  computation and the place most likely to need a new helper lemma about the
  projX↔projY transition derivative near `y=0`.
- **M3.2 (growth exponent)** — getting `N/2−2` exactly (not off-by-one) from
  the Möbius/`infReverse` factor. Cross-check against `infReverse`'s
  `reflect (N/2−2)`.
- **M0.3 (G's representation)** — a wrong domain/sheet choice makes M1–M2
  awkward. Worth a short spike before committing.

## Recommended order
1. **M0** (foundations + the `G` design spike).
2. **M1** (analytic off branch locus) — first real, self-contained chunk.
3. **M3** before **M2**: the infinity growth bound (M3) is more self-contained
   than the branch-point removability (M2); doing it first de-risks M4 and
   leaves the hardest piece (M2) last with everything else in place.
4. **M2**, then **M4**.

Total: **~6–8 weeks** focused, dominated by M2 and M3. Optionally do the
**L3 propagation** in parallel — it's independent and collapses an axiom.
