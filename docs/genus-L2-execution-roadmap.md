# Liouville L2 — execution roadmap

*Authored 2026-06-01.* Concrete, lemma-by-lemma plan for proving
`AX_HyperellipticForm_polynomial_decomposition` (Liouville L2), the last hard
gap toward a fully axiom-clean even-genus theorem. Companion to the scoping
doc [`genus-L2-L3-discharge-plan.md`](genus-L2-L3-discharge-plan.md); this one
is the *how*, with signatures and an order to execute against.

## Strategy — corrected after the M0.3 design spike (2026-06-01)

> **The "avoid the involution" plan was wrong.** Starting M0 revealed that
> σ-anti-invariance is *intrinsic* to L2, not optional. **Proof:** L2 asserts
> a single `g` with `coeff(q,z) = g(z) / squareLocalHomeomorph_a.symm(f z)`
> for *every* smooth-Y `a`. Over one `z`, the two sheets `a = (x,+√f)` and
> `a' = (x,−√f)` give the `+` and `−` branches, so L2 forces
> `coeff(q',z) = g(z)/(−√f) = −coeff(q,z)`. I.e. **L2 ⟹ `coeff(σq,·) =
> −coeff(q,·)` (σ-anti-invariance)** — so it must be *proven* en route, and
> cannot "emerge from the branch-point analysis" (which only gives
> analyticity/removability, never the sheet-negation).

So the central, hardest piece is establishing σ-anti-invariance of an
arbitrary holomorphic differential. The route that leverages our assets:

1. **Build the hyperelliptic involution `σ`** on `HyperellipticEvenProj`
   (`σ(x,y)=(x,−y)`; the even side has none — only the odd side does). Show
   `σ` is holomorphic (`ContMDiff`) and involutive.
2. **Anti-invariance via `ℙ¹`-descent** (uses our **proven** `genus ℙ¹ = 0`):
   `ω + σ*ω` is σ-invariant, hence descends to a holomorphic 1-form on the
   quotient `HyperellipticEvenProj / σ ≅ ℙ¹`; `genus ℙ¹ = 0` ⇒ that form is
   `0` ⇒ `σ*ω = −ω`. *(Needs the quotient map and form-descent — substantial.)*
   A more hands-on alternative: show `coeff(q,·) + coeff(σq,·)` is the
   chart-coefficient of a form pulled back from `ℙ¹`, hence `0`.

Only **with** σ-anti-invariance in hand does the rest go through: define
`g(z) := coeff(q,z) · √f(z)` from one sheet, and anti-invariance gives the
formula on the other sheet automatically. Then `g` is entire (branch points
removable, Mathlib:
`Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`) with
polynomial growth (infinity chart) ⇒ a polynomial (`differentiable_eq_polynomial_of_growth`).

**Gemini cross-check (gemini-2.5-pro, 2026-06-01) — estimate revised DOWN.**
The descent to `ℙ¹` is **not** needed: the direct-Liouville argument for
"a σ-invariant holomorphic 1-form is `0`" is confirmed sound and complete
(single-valued `c(x)`; entire via removable singularities at branch points;
`c = O(1/x²)` at the two infinity points; `c ≡ 0` by our Liouville). It is a
pure chart computation reusing assets we already have — **no quotient map,
no form-pushforward.** And σ itself is medium-difficulty (identity in projX
coords; `y↦−y` at branch points; swaps the two `∞` points). So the realistic
range is **~1–2 months**, not 2–3, dominated by: building σ and a *concrete*
`σ*` on the cocycle representation (do **not** use the axiomatized
`pullbackOneForm` — define it directly: `(σ*ω).coeff q z = ω.coeff (σq) z`
since σ is `x↦x` in projX coords), then the (now reusable) branch/infinity
Liouville bookkeeping. M2/M3 still follow.

**Warning — the tempting "cheaper route" is circular.** Gemini's first
suggestion ("posit `{x^k dx/y}`, prove independent, conclude basis since
`dim H⁰(Ω) = g`") **assumes the upper bound `dim ≤ g`** — exactly what L2/L3
establishes. We have only the *lower* bound (S7) + finite-dimensionality
(Montel); `dim = g` is the goal. That route is Riemann–Roch in disguise. There
is **no free lunch for the upper bound**: it requires either σ-anti-invariance
(the direct-Liouville route above) or Riemann–Roch.

### Down payment landed
- **M0.1** `squareLocalHomeomorph_symm_eval_analyticOn` (`AffineForm.lean`) —
  the `√f` branch is analytic on the projX target. Real, axiom-free; valid
  regardless of the strategy correction.

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

## Recommended order (revised 2026-06-01)
1. **M0** — done: design spike (which produced the strategy correction above)
   + `M0.1` landed.
2. **Mσ — σ-anti-invariance** (the new central, hardest milestone): build the
   even-side involution `σ`, prove holomorphic + involutive, then
   `σ*ω = −ω` via `ℙ¹`-descent (uses `genus ℙ¹ = 0`). *Everything downstream
   depends on this.*
3. **M1** (`G` analytic off branch locus) + **M0.1** — straightforward once Mσ
   gives well-definedness across sheets.
4. **M3** (infinity growth) before **M2** (branch-point removability).
5. **M4** — assemble (`differentiable_eq_polynomial_of_growth`, done).

Total: **~1–2 months** (revised down after the Gemini cross-check — the
quotient descent is avoided), dominated by **Mσ** (build σ + concrete `σ*` +
the direct-Liouville vanishing of σ-invariant forms). The **L3 propagation**
remains independent and tractable (~1 week, uses `hyperellipticForm_coeff_projX`).

**Mσ, concretely:**
- `σ : HyperellipticEvenProj H → HyperellipticEvenProj H`, `(x,y)↦(x,−y)`;
  prove involutive + `ContMDiff` (identity in projX coords — easy; `y↦−y` at
  branch points; swaps the two `∞` points).
- `pullbackInvolution : HolomorphicOneForm → HolomorphicOneForm`, defined
  *concretely* on the cocycle: `(σ*ω).coeff q z = ω.coeff (σq) z` (no axiom).
- `sigma_invariant_form_eq_zero`: a σ-invariant holomorphic 1-form is `0`
  (the direct-Liouville chart argument; reuses `liouville_*` + the
  branch/infinity bookkeeping). ⇒ `σ*ω = −ω`.
- Then `a := ω.coeff·√f` from one sheet; anti-invariance gives the other;
  entire + growth ⇒ polynomial ⇒ L2.

**Decision note.** Even at ~1–2 months this is a campaign. Worth weighing
against (b) the Riemann–Roch upper bound directly, or (c) banking even-genus
*sound modulo L2/L3* and spending effort on higher-certainty wins
(`ofCurve_inj` anti-hack, Class-1 vetting). But the cost is now correctly
understood, and the path is concrete.
