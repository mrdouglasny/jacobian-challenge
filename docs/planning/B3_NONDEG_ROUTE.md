# B-3: Period non-degeneracy — statement-level design

Status: DESIGN (written before implementation; orchestrator may DT-vet mid-flight)
Branch: `feat/period-nondegeneracy`
Date: 2026-06-11

## Goal

First pillar of the independent `AX_PeriodCycleBasis` route: **no nonzero
ℝ-linear functional kills all periods of closed loops**, equivalently the
ℝ-span of the period functionals of closed analytic loops is all of
`(HolomorphicOneForm X →ₗ[ℂ] ℂ)` (≅ ℂ^g).

Route idea: **Forster, *Lectures on Riemann Surfaces*, §21 (Jacobi variety),
Lemma 21.4 — the dissection-free maximum-principle argument.** Suppose
`Λ = Re⟨d,·⟩` kills all loop periods. Then
`u(Q) := Λ(∫_{x₀→Q} ω-vector)` is (a) *well defined as a literal Lean
function* — in our substrate the path functional is the **defined**
`arcPeriodFunctional (bridgePathArc x₀ Q)`, so no well-definedness quotient
is ever needed; (b) continuous and locally the real part of a holomorphic
chart primitive *because* Λ kills the correction loops; (c) constant by the
maximum principle (open-mapping dichotomy) + clopen argument on compact
connected X; whence the associated form `η = ∑ dⱼ ωⱼ` has all chart
primitives constant, so `η = 0`, so `Λ = 0`.

Written **independently in our tree** (`Jacobians/RiemannSurface/*`,
`Jacobians/Bridge/BridgePathArc` consumer); no code copied from any external
tree.

## Headline statements

With `W := HolomorphicOneForm X →ₗ[ℂ] ℂ` (an ℝ-module via
`Module ℝ ℂ` + `SMulCommClass`), `x₀ : X`, X compact connected Riemann
surface:

```lean
/-- The period functional of a closed analytic loop. -/
noncomputable def loopPeriodFunctional (x₀ : X) (γ : AnalyticLoop X x₀) :
    HolomorphicOneForm X →ₗ[ℂ] ℂ :=
  arcPeriodFunctional γ.arc
    (fun form => analyticArc_canonicalIntegrand_intervalIntegrable γ.arc form)

-- H1 (engine, functional form)
theorem eq_zero_of_forall_loopPeriodFunctional_eq_zero (x₀ : X)
    (Λ : (HolomorphicOneForm X →ₗ[ℂ] ℂ) →ₗ[ℝ] ℝ)
    (hΛ : ∀ γ : AnalyticLoop X x₀, Λ (loopPeriodFunctional x₀ γ) = 0) :
    Λ = 0

-- H2 (span form; the honest "non-degeneracy")
theorem span_loopPeriodFunctional_eq_top (x₀ : X) :
    Submodule.span ℝ (Set.range (loopPeriodFunctional x₀)) = ⊤
```

These statements do **not** mention `AX_PeriodCycleBasis`.

**Outcome (2026-06-11, verified):** the axiom closure of H1/H2 is exactly
`[propext, Classical.choice, Quot.sound]` — no project axioms at all (the
`FiniteDimensional ℂ (HolomorphicOneForm X)` instance is the Kirov-Montel
bridge-derived theorem, itself axiom-free at the current pin). C1–C3 add
exactly `Jacobians.Axioms.AX_PeriodCycleBasis` and nothing else.

## Downstream corollaries (what Layer3/Periods + lattice instances consume)

```lean
-- C1: non-degeneracy over the CHOSEN PeriodCycleBasis loops' arc periods
theorem span_choiceCycleBasis_arcPeriodFunctional_eq_top (x₀ : X) :
    Submodule.span ℝ (Set.range fun i : Fin (2 * genus X) =>
      arcPeriodFunctional ((Classical.choice (AX_PeriodCycleBasis x₀)).loops i).arc
        (fun form => AX_cycleBasisLoop_integrable x₀ _ i form)) = ⊤

-- C2: the H1-level period image spans
theorem span_range_loopIntegralToH1_eq_top (x₀ : X) :
    Submodule.span ℝ (Set.range (loopIntegralToH1 x₀)) = ⊤

-- C3: coordinate form — the "span half" of IsZLattice for the period lattice
theorem span_periodLatticeInBasis_eq_top (x₀ : X)
    (b : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) :
    Submodule.span ℝ ((periodLatticeInBasis X x₀ b : Set (Fin (genus X) → ℂ))) = ⊤
```

C1–C3 route through the chosen witness only to *identify* loop functionals
with `loopIntegralToH1` values (`LoopIntegralHom` lemmas:
`loopDevValH1Hom_loopToHomology` + `loopDevValH1Hom_eq_loopIntegralToH1_apply`),
so they inherit `AX_PeriodCycleBasis` in their closure — that is expected and
honest: the *statements* downstream consumes are about the chosen basis. The
engine H1/H2 is the independent pillar that the eventual discharge route will
instantiate on *constructed* loops.

C3 is exactly the `IsZLattice.span_top` half of
`periodLatticeInBasis_isZLattice`, now obtained from the maximum principle
instead of from the bundled R2 field — pillar 1 of replacing
`AX_PeriodCycleBasis`. (Pillar 2, discreteness, is out of scope here.)

## Proof architecture (all pieces inventoried against the existing substrate)

### New file `Jacobians/RiemannSurface/ChartSegmentArc.lean`

The only genuinely new geometric object: for `Q ∈ chartBallSource P` (the
existing `Bridge.BridgePath` chart-ball machinery: `chartTargetBallRadius`,
`chartBallSource`, open, contains `P`), the straight chart segment from `P`
to `Q`, endpoint-flattened, as an `AnalyticArc`:

* `chartSegmentPath P Q hQ : Path P Q`,
  `t ↦ (chartAt ℂ P).symm (flatSegment (chartAt ℂ P P) (chartAt ℂ P Q) t)` —
  mirrors `PathChartBallSubdivision.chartFlatPath` (segment stays in the ball
  by convexity: `segment_subset_ball`, `flatSegment_mem_segment`).
* `chartSegmentArc P Q hQ : AnalyticArc X` with partition `{0,1}` — mirrors
  `PathChartBallSubdivision.chartFlatAnalyticArc` (strong witness:
  `U := univ`, `f := flatSegment`, `analyticAt_flatSegment`).
* Endpoint/`mem_source`/`mem_ball` simp lemmas.
* **Segment FTC**: for any primitive `g` of `form.coeff P` on the chart ball,
  ```lean
  canonicalArcIntegral (chartSegmentArc P Q hQ) form
    = g ((extChartAt 𝓘(ℂ) P) Q) - g ((extChartAt 𝓘(ℂ) P) P)
  ```
  via the existing B1 lemma
  `canonicalArcIntegral_eq_chartPrimitive_endpoint_sub` (DevelopingMap.lean).
  Side conditions: chart trace `=ᶠ flatSegment` on `Ioo 0 1`
  (`right_inv` + `Path.extend`), `HasDerivWithinAt` from
  `hasDerivAt_flatReparam`, integrability by continuity of
  `coeff ∘ flatSegment · flatSegment'` plus a.e. agreement on `Ioo`
  (same pattern as
  `analyticArc_canonicalIntegrand_refined_cell_intervalIntegrable`).

### New file `Jacobians/RiemannSurface/PeriodNondegeneracy.lean`

* `basepointPeriodFunctional x₀ Q : W :=
   arcPeriodFunctional (bridgePathArc x₀ Q) (integrability)` — our own
  tight-closure copy of the `pathIntegralBasepointFunctional` idea (linearity
  from `canonicalArcIntegral_add/_smul` + the proven integrability lemma; we
  do NOT route through `kirovBackedFunctional` to keep the closure minimal).
* **E1 (increment identity, exact, functional-level).** For
  `Q ∈ chartBallSource P` define
  `incrementLoop x₀ P Q hQ : AnalyticLoop X x₀ :=
   ((bridgePathArc x₀ P).trans (chartSegmentArc P Q hQ)).trans
   (bridgePathArc x₀ Q).reverse` (existing `ArcAlgebra.trans/.reverse`).
  Then, by `canonicalArcIntegral_trans/_reverse` (formwise, then
  `LinearMap.ext`):
  `basepointPeriodFunctional x₀ Q
     = basepointPeriodFunctional x₀ P
       + arcPeriodFunctional (chartSegmentArc P Q hQ) _
       - loopPeriodFunctional x₀ (incrementLoop x₀ P Q hQ)`.
  This is the `AX_Period_Triangle` proof pattern, re-run with the segment.
* **E2 (u and its local formula).** Given `Λ` with `hΛ`:
  `u Q := Λ (basepointPeriodFunctional x₀ Q)`; E1 + `hΛ` give
  `u Q = u P + Λ (arcPeriodFunctional (chartSegmentArc P Q hQ) _)`.
* **E3 (Λ in coordinates).** `bω := Module.finBasis ℂ (HolomorphicOneForm X)`
  (size `genus X`; `instFiniteDimOneForms`). Set
  `c j := (Λ (bω.coord j) : ℂ) - Complex.I * Λ (Complex.I • bω.coord j)`
  (with `bω.coord j = bω.dualBasis j`). Then for every `F : W`:
  `Λ F = (∑ j, c j * F (bω j)).re` (expand `F` by `dualBasis.sum_repr`,
  split scalars `z = re z + I * im z`, ℝ-linearity).
* **E4 (the candidate form).** `η := ∑ j, c j • bω j`;
  `η.coeff P z = ∑ j, c j * (bω j).coeff P z` (Submodule coe of finite sums).
* **E5 (local holomorphic model).** Per `P : X`, the `PathChartBall`
  `B P := ⟨P, chartAt P P, chartTargetBallRadius P, _⟩` and the canonical
  primitives `g j := pathChartBallPrimitive (bω j) (B P)`
  (`pathChartBallPrimitive_hasDerivAt`). `H_P z := ∑ j, c j * g j z`:
  `HasDerivAt H_P (η.coeff P z) z` on the ball. Combining E2 + E3 + segment
  FTC: for `Q ∈ chartBallSource P`,
  `u Q = u P + (H_P (chart P Q)).re - (H_P (chart P P)).re`.
* **E6 (continuity).** From E5's formula, `u` is continuous on each
  `chartBallSource P`, hence on `X`.
* **E7 (maximum + clopen).** `u` attains a max `M` on compact `X`
  (`IsCompact.exists_isMaxOn`); `S := {x | u x = M}` is closed, nonempty,
  and open: at `P ∈ S`, `Re H_P` has a local max at the chart center, and
  Mathlib's open-mapping dichotomy
  `AnalyticAt.eventually_constant_or_nhds_le_map_nhds`
  (`H_P` is `DifferentiableOn` on the ball ⇒ `AnalyticAt`) forces
  `H_P` locally constant (the second branch would make the closed half-plane
  `{Re ≤ Re H_P(center)}` a neighborhood of `H_P(center)` — false). So `u`
  is locally `M`. `IsClopen.eq_univ` (connected) ⇒ `u` constant.
* **E8 (center derivative vanishes).** `u` constant ⇒ `Re H_P` constant on
  the whole ball (the chart is a bijection `chartBallSource P ↔ ball`),
  hence by the same dichotomy at the center `H_P` is eventually constant ⇒
  `deriv H_P (center) = 0` ⇒ `η.coeff P (chartAt P P) = 0` — at **every** `P`.
* **E9 (forms vanishing at all chart centers are 0).** New small lemma in
  the same file: if `form.coeff y ((extChartAt 𝓘(ℂ) y) y) = 0` for all `y`,
  then `form = 0`. Pointwise: off-target coeff is 0 by `IsZeroOffChartTarget`;
  on-target at `z`, apply `SatisfiesCotangentCocycle` with
  `y := (extChartAt x).symm z` — the right-hand side's coefficient factor is
  the coeff of `y` **at its own center**, which vanishes. No identity theorem
  needed.
* **E10 (wrap-up).** `η = 0` ⇒ all `c j = 0` (basis) ⇒ `Λ = 0` by E3.
  H2 from H1 by quotient + dual separation
  (`Module.forall_dual_apply_eq_zero_iff` over ℝ).

### New file `Jacobians/Layer3/PeriodSpan.lean` (corollaries C1–C3)

* every `loopPeriodFunctional x₀ γ = loopIntegralToH1 x₀ (loopToHomology γ)`
  (existing `LoopIntegralHom` lemmas), and `loopIntegralToH1` of any `H1`
  class lies in the ℤ-span of the 2g chosen-loop functionals
  (`Basis.span_eq` + `Submodule.map_span` + `loopIntegralToH1_loop`);
  ℤ-span ⊆ ℝ-span (`Submodule.span_subset_span`). Gives C1, C2.
* C3 by transporting C2 along `b.dualBasis.equivFun` (`Submodule.map_span`,
  surjectivity of the coordinate equivalence).

## Honest-scoping policy

No `sorry` anywhere. If a piece resists at implementation time, it lands as a
**named hypothesis** on the affected theorem (documented here and in the
progress log), never as a sorry/axiom. Current assessment after full
inventory: every needed primitive exists (listed above with file names); no
named hypotheses are expected.

**Outcome (2026-06-11):** everything closed; **zero named hypotheses, zero
sorries, zero new axioms**. Landed files:
`Jacobians/RiemannSurface/ChartSegmentArc.lean`,
`Jacobians/RiemannSurface/PeriodNondegeneracy.lean`,
`Jacobians/Layer3/PeriodSpan.lean` (all registered in the umbrella imports;
full `lake build` green).

## Gates

* standard-3 (`lake env lean` per file; commit per compiling piece;
  `#print axioms` on the headlines at the end).
* No new port (`Jacobians.Vendor.*`) imports except through modules that the
  consumed our-side files already import (`Bridge.BridgePathArc` already
  imports `Bridge.KirovLineIntegral`; we add no direct `Vendor` import).
* Progress: `docs/planning/B3_PROGRESS.log`. No push.

## References

* O. Forster, *Lectures on Riemann Surfaces*, GTM 81, §21 (esp. the
  non-degeneracy lemma 21.4: a real-linear functional vanishing on all
  periods has a global single-valued potential, which is locally the real
  part of a primitive of a holomorphic form, hence constant by the maximum
  principle; therefore the form vanishes).
* Mathlib: `Complex.IsExactOn` / `Mathlib.Analysis.Complex.HasPrimitives`
  (already consumed by `DevelopingMap.lean`),
  `AnalyticAt.eventually_constant_or_nhds_le_map_nhds`
  (`Mathlib.Analysis.Complex.OpenMapping`),
  `Module.forall_dual_apply_eq_zero_iff`.
