# Codex plan — Mσ.3: concrete `pullbackInvolution`

*Authored 2026-06-02 (Claude). Executable recipe for the σ-pullback on the
cocycle representation, replacing the axiomatized `pullbackOneForm` for the
hyperelliptic involution. Prereq DONE: `hyperellipticEvenInvol_contMDiff`
(Mσ.2, commit `3890d91`). File to edit:
`Jacobians/ProjectiveCurve/Hyperelliptic/Involution.lean` (or a new
`…/Hyperelliptic/InvolutionPullback.lean` importing it + `RiemannSurface.OneForm`
+ `EvenForm`).*

## ⚠ Correction to `genus-L2-execution-roadmap.md` (READ FIRST)

The roadmap says: *"define `(σ*ω).coeff q z = ω.coeff (σq) z` since σ is `x↦x`
in projX coords (derivative 1)."* **That naive formula is WRONG as a submodule
element.** It satisfies the cotangent cocycle only on the smooth-Y (projX)
charts, where σ's chart representative is `z↦z`. But the submodule conditions
quantify over **all** `q`, including:
- **branch points** (`f(x₀)=0`): there the chart is projY, the coordinate is
  `y`, and σ acts as `y↦−y` — derivative **−1**, not 1. (Note branch points are
  σ-**fixed**: `a.invol = a` since `y=0`, yet the chart map is still `z↦−z`.)
- **the two ∞ points**: σ **swaps** them, and the ∞-chart coordinate `u` maps
  with its own derivative.

So the naive family fails the cocycle off the smooth-Y locus and is not in
`holomorphicOneFormSubmodule`. **Use the honest, uniform pullback formula below**
— it is correct at every point automatically, no case-split in the definition.
The derivative factor *evaluates* to `1` on projX charts (giving the roadmap's
formula there, which is all Mσ.4 actually consumes) and to `−1`/etc. elsewhere.

## The definition (uniform; correct everywhere)

```lean
open scoped Manifold ContDiff
-- abbreviations: σ := hyperellipticEvenInvol H, eq q := extChartAt 𝓘(ℂ,ℂ) q

noncomputable def pullbackInvolutionCoeff (H) [Fact (¬ Odd H.f.natDegree)]
    (form : HolomorphicOneForm (HyperellipticEvenProj H)) :
    HyperellipticEvenProj H → ℂ → ℂ :=
  fun q z =>
    form.coeff (hyperellipticEvenInvol H q)
        ((extChartAt 𝓘(ℂ,ℂ) (hyperellipticEvenInvol H q))
          (hyperellipticEvenInvol H ((extChartAt 𝓘(ℂ,ℂ) q).symm z)))
      * fderiv ℂ ((extChartAt 𝓘(ℂ,ℂ) (hyperellipticEvenInvol H q)) ∘
            hyperellipticEvenInvol H ∘ (extChartAt 𝓘(ℂ,ℂ) q).symm) z 1
```
This is the classical `(σ*ω) = ω∘dσ` written in the cocycle representation:
`A_q z := eq(σq)(σ((eq q).symm z))` is "follow σ into the target chart",
`B_q z := fderiv(eq(σq) ∘ σ ∘ (eq q).symm) z 1` is the chart-derivative of σ.

Note `eq(σq) ∘ σ ∘ (eq q).symm` is exactly `writtenInExtChartAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) q σ`
(`Mathlib...ContMDiff/Defs`), so all of Mσ.2's smoothness lands directly on it.

## Submodule membership — three obligations

`pullbackInvolutionCoeff H form ∈ holomorphicOneFormSubmodule (HyperellipticEvenProj H)`,
i.e. `⟨IsHolomorphicOneFormCoeff, SatisfiesCotangentCocycle, IsZeroOffChartTarget⟩`.

### (1) `IsHolomorphicOneFormCoeff` — analyticity on each target
For each `q`: `AnalyticOn ℂ (pullbackInvolutionCoeff H form q) (eq q).target`.
The coeff is `(form.coeff (σq) ∘ A_q) · B_q`. Build analyticity of the three
factors on `(eq q).target`:
- **σ's chart rep is analytic.** From `hyperellipticEvenInvol_contMDiff H` and
  `contMDiffAt_iff` (Defs.lean:181) / `contMDiffOn_iff` (Defs.lean:478), the
  written-in-chart map `eq(σq) ∘ σ ∘ (eq q).symm` is `ContDiffOn ℂ ω` on
  `(eq q).symm ⁻¹' (σ-source) ∩ range I`; convert to `AnalyticOn` via
  `contDiffOn_omega_iff_analyticOn` (referenced in the handoff; it's the
  `ω`-level bridge). Call this map `Sq : ℂ → ℂ`; `A_q = Sq` on target.
- **`B_q = fderiv Sq · 1` is analytic.** `AnalyticOnNhd.fderiv`
  (`FDeriv/Analytic.lean:261`) — needs `AnalyticOnNhd` on an *open* nbhd; use
  `(eq q).open_target` + `AnalyticOn.fderivWithin` (`:356`) with
  `UniqueDiffOn` (open ⇒ `IsOpen.uniqueDiffOn`), or pass to `AnalyticOnNhd` on
  the open target. The map `w ↦ fderiv Sq w 1` is `(AnalyticOnNhd.fderiv …)`
  post-composed with the continuous-linear eval-at-`1` (`ContinuousLinearMap`
  apply is analytic).
- **`form.coeff (σq) ∘ A_q` analytic.** `form.coeff (σq)` is `AnalyticOn` on
  `(eq σq).target` (that's `form.2.1 (σq)`, i.e. `IsHolomorphicOneFormCoeff`).
  `A_q = Sq` maps `(eq q).target` into `(eq σq).target` (σ maps q-chart into
  σq-chart; check `MapsTo` from `σ`'s being a chart-to-chart map — use
  `(eq q).symm` lands in `q.source`, `σ` maps into `σq`-nbhd, `eq σq` lands in
  target). Then `AnalyticOn.comp`.
- Product: `AnalyticOn.mul`.

### (2) `SatisfiesCotangentCocycle` — the chain-rule core (heaviest)
For `q q'`, `z ∈ (eq q).target`, `(eq q).symm z ∈ (eq q').source`:
```
pbCoeff q z  =  pbCoeff q' (eq q' ((eq q).symm z)) · fderiv(eq q' ∘ (eq q).symm) z 1
```
Strategy — **functoriality**: substitute the definition on both sides and reduce
to ω's own cocycle at `(σq, σq')` plus the chain rule. Concretely:
- `pbCoeff q z = form.coeff(σq)(A_q z) · B_q z`.
- Apply ω's cocycle (`form.2.2.1`, `SatisfiesCotangentCocycle`) at `x:=σq`,
  `y:=σq'`, point `A_q z ∈ (eq σq).target`, with back-image in `(eq σq').source`
  (holds because σ maps the overlap `q∩q'` to `σq∩σq'`): this rewrites
  `form.coeff(σq)(A_q z) = form.coeff(σq')(A'_qq' z) · fderiv(eq σq' ∘ (eq σq).symm)(A_q z) 1`
  where `A'_qq' z = eq σq'((eq σq).symm (A_q z))`.
- **Chain-rule glue.** The two derivative factors `B_q z` and
  `fderiv(eq σq' ∘ (eq σq).symm)(A_q z) 1` compose, via `fderiv.comp`
  (`fderiv_comp`, with differentiability side-goals discharged from the
  analytic/`ContDiffAt` facts above), into
  `fderiv(eq σq' ∘ σ ∘ (eq q).symm) z 1`. Meanwhile the target side
  `pbCoeff q' (W z) · fderiv(eq q' ∘ (eq q).symm) z 1` expands to
  `form.coeff(σq')(A_{q'}(W z)) · B_{q'}(W z) · fderiv(eq q'∘(eq q).symm) z 1`,
  whose derivative product is `fderiv(eq σq' ∘ σ ∘ (eq q).symm) z 1` by the SAME
  chain rule (σ∘(eq q').symm ∘ eq q' ∘ (eq q).symm collapses since
  `(eq q').symm ∘ eq q' = id` near the point). Match the two sides:
  `A_q z`-vs-`A_{q'}(W z)` agree because both `= eq σq' (σ((eq q).symm z))`
  (σ well-defined on the point, independent of the q' chart used). Close by
  `ring`/`mul_comm` once the fderiv's are shown equal (`fderiv` congruence via
  `Filter.EventuallyEq.fderiv_eq`, as in `EvenForm.lean:1112`).
- **Reuse:** `EvenForm.lean`'s `cocycle_lifted_through_lift_openEmbedding`
  (`:201`) and the `fderiv`/`Filter.EventuallyEq.fderiv_eq` patterns (`:480`,
  `:1103`) are the closest existing templates — mirror their structure.

  *This obligation is the bulk of the work (~120–200 LOC of fderiv calculus).*
  If full generality fights back, an acceptable intermediate is to prove the
  cocycle **only relating projX↔projX charts** and treat branch/∞ via the
  zero-off-target + density — BUT that does not give a submodule element, so
  only fall back to it if you also restructure Mσ.4 to not need σ* as a bundled
  `HolomorphicOneForm`. Prefer the honest full proof.

### (3) `IsZeroOffChartTarget`
For `z ∉ (eq q).target`: `pbCoeff q z = 0`. The factor `form.coeff(σq)(A_q z)`:
when `z ∉ (eq q).target`, `(eq q).symm z` is junk, but cleaner is — the whole
coeff is a product and we need one factor 0. Easiest: show `B_q z = 0` off
target? Not generally. Instead define `pbCoeff` to be `0` off-target by an
`if z ∈ (eq q).target` guard, OR prove `form.coeff(σq)(A_q z)=0` using that
`A_q z ∉ (eq σq).target` off-target (since `Sq` maps target↔target
bijectively, off-target z gives off-target image) + `form.2.2.2` (ω's
`IsZeroOffChartTarget`). The guard route is simplest and standard here — match
how `hyperellipticEvenCoeff` handles it in `EvenForm.lean`.

## Package as a linear map

```lean
noncomputable def pullbackInvolution (H) [Fact (¬ Odd H.f.natDegree)] :
    HolomorphicOneForm (HyperellipticEvenProj H) →ₗ[ℂ]
      HolomorphicOneForm (HyperellipticEvenProj H) where
  toFun form := ⟨pullbackInvolutionCoeff H form, membership-proof⟩
  map_add'  := by intro f g; ext q z; simp [pullbackInvolutionCoeff, …]; ring
  map_smul' := by intro c f; ext q z; simp [pullbackInvolutionCoeff, …]; ring
```
`map_add'`/`map_smul'` are pointwise on `coeff` (the `form.coeff(σq)` factor is
additive/homogeneous; the `B_q` factor doesn't involve `form`). Use
`HolomorphicOneForm.coeff_add`/`coeff_smul` + `ext_of_coeff`.

## Simplification lemmas for Mσ.4 (prove these too — they're what L2 consumes)

On the **smooth-Y (projX) charts**, σ's rep is `z↦z`, so:
```lean
lemma pullbackInvolutionCoeff_projX (…hq : q is smooth-Y…) (z ∈ target) :
    pullbackInvolutionCoeff H form q z = form.coeff (hyperellipticEvenInvol H q) z
```
Proof: on these charts `A_q z = z` and `B_q z = fderiv id z 1 = 1`. Extract
`A_q = id`, `B_q = 1` from the Mσ.2 fact that the affine rep on `smoothLocusY`
is `z↦z` (the `hFun`/`contDiffWithinAt_invol_writtenIn_affineChartAt` content —
generalize the `=ᶠ id` computation already in `contMDiffAt_invol`). This is the
bridge that turns the honest pullback back into the roadmap's "naive" formula
exactly where Mσ.4 needs it.

## Verify-as-you-go (CLAUDE.md)
- `lean_run_code` with `#check` matching the exact signature (`[Fact …]` as
  instance arg, not `haveI` in the test TYPE).
- Before push of ≥20 LOC: `lake env lean <file>` then `lake build`.
- `#print axioms pullbackInvolution` — expect core 3 +
  `contDiffOn_symm_toOpenPartialHomeomorph` + the two cross-summand compat
  axioms (same footprint as `hyperellipticEvenInvol_contMDiff`). Must **not**
  introduce `pullbackOneForm`/`pushforwardOneForm` or `sorryAx`.

## Then → Mσ.4, Mσ.5, L2
Back to [`Msigma-codex-handoff.md`](Msigma-codex-handoff.md) §Mσ.4
(`sigma_invariant_form_eq_zero`, direct-Liouville) → Mσ.5
(`pullbackInvolution_eq_neg`) → L2.
