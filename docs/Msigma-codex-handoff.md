# Mσ handoff — finishing the hyperelliptic involution + σ-anti-invariance

*For Codex / any contributor. Authored 2026-06-02 by the session that built
Mσ part 1.* Goal: complete **Mσ** toward axiom-clean even-genus (Liouville L2).
Context: [`genus-L2-execution-roadmap.md`](genus-L2-execution-roadmap.md) (read
the "Strategy — corrected" and "Mσ, concretely" sections; the Gemini
cross-check validated the direct-Liouville route — **no quotient construction
needed**).

## Verify-as-you-go
- Per-file: `lake env lean Jacobians/ProjectiveCurve/Hyperelliptic/Involution.lean`
  (~30s incremental). Then `lake build` for the whole graph (CI parity).
- Axiom hygiene: every new theorem must be `#print axioms`-clean
  (`[propext, Classical.choice, Quot.sound]` only) — **do NOT** introduce or
  consume the axiomatized `pullbackOneForm`/`pushforwardOneForm`. Define the
  pullback concretely.
- The pre-push rule in `CLAUDE.md` applies: validate with `lake env lean`
  before pushing ≥20 LOC of real Lean.

## Already done (in `Jacobians/ProjectiveCurve/Hyperelliptic/Involution.lean`)
- `HyperellipticAffine.invol` / `HyperellipticAffineInfinity.invol`: `(·,y)↦(·,−y)`,
  `@[simp] invol_val`, `invol_invol`.
- `hyperellipticEvenInvolPre := Sum.map invol invol`; respects the glue
  (`hyperellipticEvenInvol_glue`) and its `EqvGen` closure
  (`hyperellipticEvenInvol_eqvGen`).
- `hyperellipticEvenInvol H : HyperellipticEvenProj H → HyperellipticEvenProj H`
  (`= Quotient.map …`), with `@[simp] hyperellipticEvenInvol_mk`
  (`σ ⟦p⟧ = ⟦involPre p⟧`, by `rfl`), `hyperellipticEvenInvol_invol`,
  `…_involutive`, `…_continuous`. All axiom-free; build green.

## Key facts / API you'll need (verified)
- **EvenProj chart.** `HyperellipticEvenProj.chartAt H h q` (in `EvenAtlas.lean`)
  is `affineLiftChart H h a` when `Quotient.out q = Sum.inl a`, and
  `infinityLiftChart H h b` when `Sum.inr b`. `affineLiftChart` lifts the affine
  curve's own chart at `a` — which is `affineChartProjX a hpY` for `a ∈ smoothLocusY`
  (`OddAtlas/AffineChart.lean:146`) and `affineChartProjY a hpX` for
  `a ∈ smoothLocusX \ smoothLocusY` (branch points). The projX coordinate is `x`.
- **√f branch.** `(squareLocalHomeomorph a hpY).symm (H.f.eval z)` is the local
  `√(f(z))` branch; nonzero on target (`squareLocalHomeomorph_symm_ne_zero`),
  analytic on the projX target (`squareLocalHomeomorph_symm_eval_analyticOn`,
  `AffineForm.lean` — M0.1, already landed).
- **Canonical coeff.** `affineProjXCoeff g a hpY z = g.eval z / (square…).symm (f.eval z)`
  on target (`affineProjXCoeff_eq_on_target`), analytic
  (`affineProjXCoeff_analyticOn_chartTarget`).
- **Form coeff.** `ω.coeff q` is `AnalyticOn ℂ · (extChartAt 𝓘(ℂ) q).target`
  (this is `ω.2.1`, `IsHolomorphicOneFormCoeff`), zero off-target
  (`ω.2.2.2`, `IsZeroOffChartTarget`), and satisfies the cotangent cocycle
  (`ω.2.2.1`). The cross-summand cocycle is now real
  (`hyperellipticEvenCoeff_cocycle_{inl_inr,inr_inl}`).
- **σ on points.** For `q = ⟦Sum.inl a⟧`, `σ q = ⟦Sum.inl a.invol⟧`,
  `a.invol.val = (a.val.1, −a.val.2)` — same `x`, negated `y`.
- **Mathlib analysis tools (confirmed present):**
  - removable singularity: `Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`,
    `…differentiableOn_update_limUnder_of_bddAbove`;
  - Liouville (manifold): `Jacobians.Axioms.HyperellipticLiouville.liouville_compact_complex_manifold`;
  - growth ⇒ polynomial: `Jacobians.GeneralResults.differentiable_eq_polynomial_of_growth`;
  - identity theorem: `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`;
  - `neg_sq`, `contDiffOn_omega_iff_analyticOn`, `contMDiffOn_extChartAt_symm`.

## Tasks (in order)

### Mσ.2 — `σ` is `ContMDiff` (holomorphic)

> **Status (2026-06-02): Mσ.2 DONE — affine summands AND quotient descent.**
> `HyperellipticAffine.contMDiff_invol` / `…AffineInfinity.contMDiff_invol` (chart
> rep `z↦z` on smoothLocusY, `z↦−z` on smoothLocusX), and now
> **`hyperellipticEvenInvol_contMDiff`** (Codex, via the maximal-atlas route in
> [`descent-codex-plan.md`](descent-codex-plan.md)). Build green; axioms =
> core 3 + `contDiffOn_symm_toOpenPartialHomeomorph` (affine IFT chart helper,
> pre-existing) + the two cross-summand `…_compat_…` axioms (already in the
> even-genus footprint, as scoped). **No new axioms.** Next: Mσ.3 below.
>
> **Corrected scoping for the descent:**
> - **Do NOT require it axiom-free.** EvenProj's smooth structure already rests
>   on `affineLiftChart_compat_infinityLiftChart` / `…_inr_…` (Class 2c), and
>   `genus_HyperellipticEven_eq` already depends on them — so σ depending on the
>   EvenProj manifold structure adds **nothing** to the even-genus footprint.
>   Use `chartAt`/`extChartAt`/`IsManifold` freely.
> - **Gotcha:** `EvenAtlas.chartAt q` uses `Quotient.out q`, which returns an
>   *arbitrary* representative of `q`'s class. For `q = ⟦inl a⟧` with `a.1 ≠ 0`
>   the class is `{inl a, inr b}` and `out q` may be the **infinity** rep `inr b`,
>   so `extChartAt ⟦inl a⟧ ≠ affineLiftChart a` in general. Plan around this:
>   either (i) prove `proj_inl`/`proj_inr` are `ContMDiff` open *local
>   diffeomorphisms* and transfer `σ ∘ proj_inl = proj_inl ∘ σ_aff` (cleanest if
>   a smooth-open-embedding transfer lemma is available), or (ii) use a
>   maximal-atlas chart-switch to `affineLiftChart a` (compatible with the atlas
>   via the proven `affineLiftChart_compat_affineLiftChart` same-summand and the
>   axiomatic cross-summand compat) and reduce to the affine representative via
>   `lift_openEmbedding_apply`/`_symm` + the commutation `hyperellipticEvenInvol_mk`.
> - **Reconsider whether ContMDiff is even on the critical path:** Mσ.3's
>   `pullbackInvolution` is defined directly on the coefficient cocycle
>   (`(σ*ω).coeff q z := ω.coeff (σq) z`); check whether its
>   submodule-membership proof needs full `ContMDiff` of σ or only the
>   chart-coordinate facts (σ fixes `x` in projX). If the latter, the
>   `ContMDiff` descent may be skippable. **Resolve this before grinding the
>   descent.**

(Original signature, if pursued:)
```lean
theorem hyperellipticEvenInvol_contMDiff (H : HyperellipticData) [Fact (¬ Odd H.f.natDegree)] :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (hyperellipticEvenInvol H)
```
Strategy: `ContMDiff` reduces to: for each `q`, the chart representative
`extChartAt (σq) ∘ σ ∘ (extChartAt q).symm` is `ContDiffOn ℂ ω` near
`extChartAt q q`. In projX coords this representative is the **identity**
`x ↦ x` (σ fixes `x`; `affineLiftChart` at `a` and at `a.invol` use the same
`x`-coordinate), at branch points it's `y ↦ −y`, and at the two `∞` points
it's the identity in `u`. Concretely: compute `extChartAt (σ q)` against
`extChartAt q` summand-by-summand (`affineLiftChart`/`infinityLiftChart`) and
show the composite is `id` (smoothLocusY), `Neg.neg` (smoothLocusX), or `id`
(infinity). Mirror the transition-map computations already in
`EvenForm.lean`/`AffineForm.lean`. **This is the most chart-bookkeeping-heavy
task.** (If `IsManifold`-level `ContMDiff` proves painful, a usable
intermediate is `MDifferentiable`, which is all the pullback needs.)

### Mσ.3 — concrete pullback `pullbackInvolution`
Define WITHOUT the `pullbackOneForm` axiom, directly on the cocycle. Since σ is
`x↦x` in projX coords (derivative 1), set, on the coefficient family,
`(σ*ω).coeff q z := ω.coeff (σ q) z`. Prove this lands in
`holomorphicOneFormSubmodule` (analyticity transfers since σ is a holomorphic
chart iso fixing the coordinate; cocycle transfers via `σ`'s chart action;
zero-off-target transfers). Package:
```lean
def pullbackInvolution (H) [Fact (¬ Odd H.f.natDegree)] :
    HolomorphicOneForm (HyperellipticEvenProj H) →ₗ[ℂ] HolomorphicOneForm (HyperellipticEvenProj H)
```
(ℂ-linear; `map_add'`/`map_smul'` are pointwise on `coeff`.) Note: because σ
fixes the projX coordinate, the chart-derivative factor is `1`, so there is
**no** Möbius/derivative subtlety here — this is genuinely just precomposition
with σ on the coefficient. Watch the branch-point/∞ charts where the
coordinate is `y`/`u`: there the derivative factor is `−1`/`1` respectively
(σ is `y↦−y` at branch points) — verify the cocycle still closes.

### Mσ.4 — `sigma_invariant_form_eq_zero` (the direct-Liouville core)
```lean
theorem sigma_invariant_form_eq_zero (H) [Fact (¬ Odd H.f.natDegree)]
    (η : HolomorphicOneForm (HyperellipticEvenProj H))
    (hinv : pullbackInvolution H η = η) : η = 0
```
Proof (validated by Gemini, gemini-2.5-pro 2026-06-01; **no quotient map**):
1. σ-invariance ⇒ on a projX chart, `η.coeff q z = η.coeff (σq) z`, but the two
   sheets over `z` carry the `+√f` and `−√f` branches; combined with the form
   being `c·dx/y`-shaped, the coefficient is a single-valued function `c(z)` of
   `x` alone. Realize `c : ℂ → ℂ` and prove well-defined.
2. `c` is **entire**: analytic off `{f=0}` (product of `η.coeff` analyticity and
   `√f` analyticity, M0.1); at each branch point `x₀` (`f(x₀)=0`, so `f'(x₀)≠0`)
   it's a **removable singularity** — in the projY chart `η = c(x)·(2y/f'(x)) dy`
   is analytic, forcing `c` bounded near `x₀`; apply
   `analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`.
3. `c → 0` at ∞: at the two `∞` points (`x=1/u`, `dx=−du/u²`), holomorphicity of
   `η` forces `c(1/u)/u²` bounded, i.e. `c(x) = O(1/x²)`.
4. Entire + `→0` at ∞ ⇒ `c ≡ 0` (Liouville: a continuous map → 0 at the
   cobounded filter is bounded, hence by `differentiable_eq_polynomial_of_growth`
   with `n=0` it's constant `=0`; or reuse the `liouville`/bounded-range helper
   from `Line/OneForm.lean`). Hence `η.coeff = 0` on every chart ⇒ `η = 0`
   (`HolomorphicOneForm.ext_of_coeff`).
The branch/∞ bookkeeping (steps 2–3) mirrors `Line/OneForm.lean`'s ℙ¹ proof and
the `EntireGrowth.lean` argument — lean on those patterns.

### Mσ.5 — anti-invariance, the corollary
```lean
theorem pullbackInvolution_eq_neg (H) [Fact (¬ Odd H.f.natDegree)]
    (ω : HolomorphicOneForm (HyperellipticEvenProj H)) : pullbackInvolution H ω = - ω
```
Proof: `η := ω + pullbackInvolution H ω` is σ-invariant
(`pullbackInvolution` is an involution: `σ*∘σ* = id`, since `σ∘σ=id`), so
`η = 0` by Mσ.4, giving `σ*ω = −ω`. (Prove `pullbackInvolution` involutive
first — pointwise from `hyperellipticEvenInvol_invol`.)

## After Mσ: the L2 payoff
With `pullbackInvolution_eq_neg`, define `a(z) := ω.coeff q z · √f(z)` from one
sheet; anti-invariance gives the formula on the other sheet; `a` is entire +
poly-growth (same machinery as Mσ.4 steps 2–3) ⇒ a polynomial of degree
`< N/2−1` (`differentiable_eq_polynomial_of_growth`). That is L2
(`AX_HyperellipticForm_polynomial_decomposition`). Then L3 via
`hyperellipticForm_coeff_projX` (already proven) + propagation
([`genus-L2-L3-discharge-plan.md`](genus-L2-L3-discharge-plan.md)).

## Gotchas
- Even degree ⇒ **two** points at infinity (`±√(leadCoeff f)` at `u=0`),
  swapped by σ. Handle both.
- `HyperellipticEvenProj`'s instances need `[Fact (¬ Odd H.f.natDegree)]` — take
  it as an instance arg (see `CLAUDE.md` "Fact-conversion" gotcha; convert the
  whole chain, not just the top).
- `Quotient.out` is noncomputable; `hyperellipticEvenInvol_mk` (σ⟦p⟧=⟦involPre p⟧)
  is the computable handle — use it, don't reason through `out`.
- `ω` here is the `ContDiff` analytic-smoothness level (`= ⊤ : WithTop ℕ∞`), not
  the form; the form variable is named to avoid the clash (see `OneForm.lean`).
