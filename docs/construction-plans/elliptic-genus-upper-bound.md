# Plan: `genus (Elliptic ω₁ ω₂ h) = 1` as a real theorem

_Drafted 2026-04-23. Target: retire `AX_genus_Elliptic_eq_one` to a
derived theorem via the Liouville / doubly-periodic argument._

## Axiom being retired

```lean
axiom AX_genus_Elliptic_eq_one (ω₁ ω₂ : ℂ) (h : LinearIndependent ℝ ![ω₁, ω₂]) :
    Jacobians.RiemannSurface.genus (Elliptic ω₁ ω₂ h) = 1
```

Location: `Jacobians/ProjectiveCurve/Elliptic/Genus.lean`.

## Existing pieces (already real, no axiom)

`Jacobians/ProjectiveCurve/Elliptic/OneForm.lean`:
- `ellipticDz : HolomorphicOneForm (Elliptic ω₁ ω₂ h)` — the invariant 1-form.
- `ellipticDz_ne_zero`
- `genus_Elliptic_pos : 0 < genus (Elliptic ω₁ ω₂ h)` (lower bound).

`Jacobians/AbelianVariety/ComplexTorus.lean`:
- `ComplexTorus.transition_fderiv_apply_one` — chart transitions on `ComplexTorus V L` have derivative 1 at overlap points.

## Classical content

Every `form : HolomorphicOneForm (Elliptic ω₁ ω₂ h)` is a scalar
multiple of `ellipticDz`. Proof: the chart-local coefficient functions
`form.coeff p : ℂ → ℂ` (analytic on chart target) patch, via the
cocycle with derivative 1, into a single holomorphic function
`α : ℂ → ℂ` satisfying `α(z + ω_i) = α(z)` (doubly periodic). α is
bounded on the fundamental parallelogram `{s ω₁ + t ω₂ | s, t ∈ [0,1]}`
(continuous image of compact), hence bounded globally (periodicity).
By Liouville, α is constant `= c`. Hence `form.coeff = c`
everywhere, so `form = c • ellipticDz` (by extensionality).

This gives `Submodule.span ℂ {ellipticDz} = ⊤`, so `finrank ≤ 1`, so
combined with `genus_Elliptic_pos` gives `genus = 1`.

## Phases

### Phase 1: Define the lift `ellipticFormLift : ℂ → ℂ`

The core technical step. Two sub-approaches:

**1a. Chart-centered via covering-map sections.** For each `z : ℂ`,
there exists a chart `(p, chartTarget p)` with `z ∈ chartTarget p`
(some choice of torus point `p` whose `liftPoint` is close enough to
`z`). Define

```lean
noncomputable def ellipticFormLift (form : HolomorphicOneForm (Elliptic ω₁ ω₂ h))
    (z : ℂ) : ℂ :=
  form.coeff (QuotientAddGroup.mk _ z) (some-z'-in-chart-target)
```

Well-definedness on overlaps: if z is in two chart targets, the
coefficients agree (cocycle + transition derivative 1). 

**Difficulty**: constructing the specific chart concretely, not via
`Classical.choose`. For `ComplexTorus`, `chartTarget p` is a ball of
fixed radius `r > 0` (from `exists_chartRadius`) around `liftPoint p`.
Not every `z : ℂ` satisfies `z ∈ chartTarget (mk z)` because
`liftPoint (mk z)` may be `z + λ` for some large `λ ∈ L`.

**Fix**: define a "chart picker" `pickChart : ℂ → Elliptic` such that
`z ∈ chartTarget (pickChart z)` always holds. Use compactness of the
fundamental parallelogram to get a FINITE chart cover, then pick via
case analysis.

Estimated effort: **3–5 days**.

**1b. Direct definition via `form.coeff · liftPoint ·`.** Simpler
formula but `liftPoint` is `Classical.choose`-based, so analytic
continuity arguments break.

Preferred: 1a.

### Phase 2: Prove `ellipticFormLift` is entire (`AnalyticOn ℂ ⊤`)

On each chart target (open ball), the lift agrees with
`form.coeff p`, which is analytic by `IsHolomorphicOneFormCoeff`.
Chart targets cover ℂ (Phase 1 construction), so the lift is
analytic everywhere.

Use `AnalyticOn.congr` + local patching + `AnalyticOn ℂ` sheaf
property (Mathlib: `AnalyticOnNhd`, `analyticOn_iff_locally`).

Estimated effort: **2 days**.

### Phase 3: Prove double periodicity

For `z : ℂ` and `i : Fin 2`:
`ellipticFormLift form (z + ω_i) = ellipticFormLift form z`.

Key: `QuotientAddGroup.mk (z + ω_i) = QuotientAddGroup.mk z` (since
`ω_i ∈ ellipticLattice`). So the chart changes from a point near `z`
to a point near `z + ω_i`, and the cocycle (with transition
derivative 1) gives agreement.

Careful proof: requires identifying that the chart transition between
the "chart containing `z`" and "chart containing `z + ω_i`" is
precisely translation by `ω_i`, combined with `transition_fderiv_apply_one`.

Estimated effort: **2 days**.

### Phase 4: Prove bounded on fundamental parallelogram

The set `{s ω₁ + t ω₂ | s, t ∈ [0, 1]}` is continuous image of `[0,1]²`
(compact) under the bilinear map, hence compact. `ellipticFormLift`
is continuous (entire), so `Continuous.norm_bound_of_IsCompact` or
`IsCompact.bddAbove_image` gives boundedness.

Estimated effort: **1 day**.

### Phase 5: Bounded globally via periodicity

From Phase 3 + Phase 4: for any `z : ℂ`, there exist `s, t ∈ [0, 1]`
and `m, n ∈ ℤ` with `z = s ω₁ + t ω₂ + m ω₁ + n ω₂`. Using
periodicity, `ellipticFormLift z = ellipticFormLift (s ω₁ + t ω₂)`.
So `‖ellipticFormLift z‖ ≤ M` where `M` is the sup on the
fundamental parallelogram.

Estimated effort: **1 day**.

### Phase 6: Apply Liouville

`Differentiable.exists_eq_const_of_bounded` (Mathlib, verified
present by Codex) gives `ellipticFormLift = Function.const ℂ c` for
some `c : ℂ`.

Estimated effort: **½ day**.

### Phase 7: Conclude `form = c • ellipticDz`

`form.coeff p z = ellipticFormLift form z = c` for all `(p, z)` in
chart targets. Hence `form.coeff = c • ellipticDz.coeff` (where
`ellipticDz.coeff = fun _ _ => 1`). By `HolomorphicOneForm.ext_of_coeff`,
`form = c • ellipticDz`.

Estimated effort: **1 day**.

### Phase 8: Assemble `genus_Elliptic_eq_one`

From Phase 7, `Submodule.span ℂ {ellipticDz} = ⊤`. By
`Module.finrank_le_one` (or similar), `finrank ≤ 1`. Combined with
`genus_Elliptic_pos`: `genus = 1`. Retire
`AX_genus_Elliptic_eq_one` to cite this theorem.

Estimated effort: **½ day**.

## Total

| Phase | Effort |
|---|---|
| 1. Lift construction | 3–5 days |
| 2. Holomorphicity | 2 days |
| 3. Double periodicity | 2 days |
| 4. Bounded on FP | 1 day |
| 5. Bounded globally | 1 day |
| 6. Liouville | ½ day |
| 7. Conclude `form = c • dz` | 1 day |
| 8. Assemble `= 1` | ½ day |
| **Total** | **~2 weeks** |

## Dependencies

- Mathlib: `AnalyticOnNhd`, `DifferentiableOn.analyticOnNhd`,
  `Differentiable.exists_eq_const_of_bounded`, `Module.finrank_le_one`
  — all present (verified by Codex probe).
- Project: `ComplexTorus.transition_fderiv_apply_one` (already
  present), `HolomorphicOneForm.ext_of_coeff` (already present),
  `genus_Elliptic_pos` (already present).

## Useful references

- Forster, *Lectures on Riemann Surfaces*, Ch. I §9 (holomorphic
  forms on complex tori).
- Silverman, *The Arithmetic of Elliptic Curves*, Ch. VI (complex
  tori and elliptic curves).
- Mumford, *Tata Lectures on Theta I*, §I.1.

## Consequence

- `AX_genus_Elliptic_eq_one` retires to a derived theorem.
- Combined with `genus_Elliptic_pos` (already done), the Elliptic
  hack-blocker is fully axiom-free at the genus-1 level.
- Template for higher-genus (plane curve, hyperelliptic) via
  analogous arguments — though those require additional
  infrastructure (residues, covering-space for non-torus curves).

## Status

Plan only. Codex agent attempted discharge 2026-04-23 but was blocked
by sandbox write permissions; overlay approach may succeed on retry.
Otherwise, ~2 weeks of focused manual Lean work.
