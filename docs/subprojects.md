# Subprojects catalog — the actual work units

*Authored 2026-06-02. The concrete catalog of self-contained contribution units
for the distributed effort (program design: [`centauro.md`](centauro.md);
theming parked — neutral terms here). Each **ready** unit has a frozen statement
that must be proved verbatim, a discharge plan, a reading list, an allowed-axiom
set, dependencies, and acceptance = `lake build` green + `#print axioms` within
allowed + no new `sorry` + signature unchanged.*

Status legend: **ready** (frozen, claimable) · **in-progress** (owned) ·
**draft** (statement not yet frozen/vetted) · **backlog** (candidate, needs
scoping before freezing).

---

## Tier B — axiom discharges (the cross-summand cocycle)

### SP-1 — `affineLiftChart_compat_infinityLiftChart`  · L · **ready**
Discharge the cross-summand (affine→infinity) chart-transition smoothness axiom.
**Frozen statement** (replace the `axiom` at `EvenAtlas.lean:243` with a proof;
namespace `Jacobians.ProjectiveCurve.HyperellipticEvenProj`):
```lean
theorem affineLiftChart_compat_infinityLiftChart
    (H : HyperellipticData) (h : ¬ Odd H.f.natDegree)
    (a : HyperellipticAffine H) (b : HyperellipticAffineInfinity H) :
    ContDiffOn ℂ ω
      (((affineLiftChart H h a).symm.trans (infinityLiftChart H h b)) : ℂ → ℂ)
      ((affineLiftChart H h a).symm.trans (infinityLiftChart H h b)).source
```
**Allowed axioms**: core 3 + `contDiffOn_symm_toOpenPartialHomeomorph` (narrow IFT
gap). No new axioms.
**Discharge plan**: the transition reduces (via `lift_openEmbedding_trans`) to the
underlying affine↔infinity chart map on the gluing overlap, which is the Möbius
`x ↦ 1/x` composed with polynomial-root (`√`) corrections. Case-split projX/projY
on each side (4 cases); on each, the map is a composition of: `Inv.contDiffOn`-style
smoothness of `x↦1/x` on `{x≠0}`, and the `squareLocalHomeomorph` √-branch
smoothness. The `reverseData` definitional equality (`CLAUDE.md` gotcha) ties the
infinity chart to an affine chart for `H` reversed.
**Reading list**: `EvenAtlas.lean:182–258` (the axioms + docstrings + the two
proven same-summand compat theorems to mirror); `AffineForm.lean:460–600`
(`squareLocalHomeomorph_symm_hasDerivAt`, the transition `hasDerivAt` lemmas);
`OddAtlas/AffineChart.lean:120–235` (`squareLocalHomeomorph`, `affineChartProjX`).
**Reusable infra**: `affineLiftChart_compat_affineLiftChart` /
`infinityLiftChart_compat_infinityLiftChart` (proven — same shape, same `simp`
glue); `lift_openEmbedding_trans`.
**Dependencies**: none. **Note**: hard (it was axiomatized precisely because
cross-chart gluing is the hard part) — split into the 4 sub-cases if needed.

### SP-2 — `infinityLiftChart_compat_affineLiftChart`  · L · **ready**
The symmetric (infinity→affine) transition. **Frozen statement**
(`EvenAtlas.lean:252`):
```lean
theorem infinityLiftChart_compat_affineLiftChart
    (H : HyperellipticData) (h : ¬ Odd H.f.natDegree)
    (b : HyperellipticAffineInfinity H) (a : HyperellipticAffine H) :
    ContDiffOn ℂ ω
      (((infinityLiftChart H h b).symm.trans (affineLiftChart H h a)) : ℂ → ℂ)
      ((infinityLiftChart H h b).symm.trans (affineLiftChart H h a)).source
```
Same allowed axioms / reading list / infra as SP-1; **dependency**: best done
*with* or *after* SP-1 (shares all machinery). Discharging both retires the only
two atlas axioms in the even-genus footprint.

---

## Tier C — the L2/L3 (anti-invariance) pipeline (dependency-ordered)

The headline gap: `AX_HyperellipticForm_polynomial_decomposition` (L2,
`HyperellipticLiouville.lean:215`) and `AX_HyperellipticOneForm_eq_form` (L3,
`:260`). Route D (`route-d-implementation-plan.md`) decomposes L2 via σ-anti-
invariance. Statements below depend on **SP-3 (P0)** finalizing `omegaDx`.

### SP-3 — P0 `omegaDx_analyticAt`  · M · **in-progress (maintainer)**
Local analyticity of the `dx`-coefficient. Stated + sorried in
`Hyperelliptic/AntiInvariance.lean`; see `route-d-implementation-plan.md §P0`.
Gates SP-4..SP-7.

### SP-4 — P1 branch-point removability  · M · **draft (pending SP-3)**
The symmetric scalar `s = omegaDx a + omegaDx a.invol` extends analytically across
branch points (the `±1/√f` cancellation). **Core tool ready**:
`GeneralResults/OddPartDslope.lean` (`analyticAt_dslope_oddPart`). Reading list:
`OddPartDslope.lean`, `AffineForm.lean:460–600`, SP-3 output. Statement frozen
once `omegaDx`'s final shape lands.

### SP-5 — P2 growth at infinity `s = O(1/x²)`  · M · **draft (pending SP-3)**
From the infinity chart; σ swaps the two ∞ points. Reading list:
`AffineInfinityForm.lean`, `Even.lean` (∞-point structure), SP-3 output.
**Independent of SP-4** — parallelizable.

### SP-6 — P3 `s ≡ 0` ⇒ anti-invariance  · L · **draft (pending SP-4, SP-5)**
Assemble `s` entire (same-sheet projX overlaps have transition derivative `1` ⇒
coefficients agree, trivial `AnalyticOn` glue), `→0` at ∞ ⇒ `s ≡ 0` by
`differentiable_eq_polynomial_of_growth` (n=0). Reading list: SP-4/SP-5 outputs,
`EntireGrowth.lean`, `Line/OneForm.lean`.

### SP-7 — P4 L2 from anti-invariance  · L · **draft (pending SP-6)**
`g := omegaDx · √f` single-valued + entire + poly-growth ⇒ polynomial deg
`< N/2−1`; discharge `AX_HyperellipticForm_polynomial_decomposition`. Then L3 via
`hyperellipticForm_coeff_projX` (proven bridge). Reading list:
`Form.lean:289–310`, `HyperellipticLiouville.lean:200–270`, SP-6 output.

---

## Tier A — small/upstreamable analysis lemmas

### SP-8 — even-analytic factors through `w²`  · M · **draft**
`f` analytic at `0` and even ⇒ locally `f = g ∘ (·²)` with `g` analytic. Mathlib-
upstreamable; companion to `OddPartDslope.lean`. (Vet the exact `=ᶠ[𝓝 0]`
statement before freezing — not yet on a critical path, so low priority.)

*(More Tier-A leaves to be carved from `EntireGrowth.lean` and the route-D
helpers as they surface.)*

---

## Backlog — candidate units (need scoping before freezing)

From [`AXIOM_AUDIT.md`](../AXIOM_AUDIT.md). **Dischargeable, geometric/analytic**
(good community candidates once specced):
- `AX_HyperellipticAffine_connected` (`Hyperelliptic/Basic.lean:101`) — path/
  irreducibility connectedness of the affine curve.
- `AX_H1_ProjectiveLine_trivial` (`Line/Witnesses.lean:43`) — feeds genus ℙ¹.
- `contDiffOn_symm_toOpenPartialHomeomorph` (`InverseFunctionTheorem.lean:9`) —
  the narrow IFT gap (used as an *allowed* axiom by SP-1/SP-2; discharging it
  upstream would tighten everything).

**Class 1 (textbook — cite/import, NOT community-dischargeable):**
`AX_RiemannRoch`, `AX_SerreDuality`, `AX_RiemannBilinear`, … — deep theorems;
leave as cited axioms, not in the catalog.

**Abel–Jacobi cluster** (`AbelJacobiMap.lean`, opaque-blocked) — `pullbackOneForm`,
`AX_ofCurve_inj`, etc.: blocked on concrete `pathIntegralBasepointFunctional`; not
catalogable until unblocked (see `docs/contracts/ofCurve.md`).

---

## Maintenance
When a unit merges: flip status → merged; if it discharged an axiom, update
`AXIOM_AUDIT.md` + README counts in the same PR. Carve new Tier-A leaves and
freeze drafts (SP-4..SP-8) as their prerequisites land.
