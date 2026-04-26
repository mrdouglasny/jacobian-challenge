# Genus theorem discharge plan

_Drafted 2026-04-26. Concrete sub-task breakdown for honestly proving
`genus_HyperellipticEven_eq` and `genus_HyperellipticOdd_eq`._

## Goal

Discharge the two open genus theorems:

* `genus_HyperellipticEven_eq` in
  [`Jacobians/Extensions/HyperellipticEven.lean`](../Jacobians/Extensions/HyperellipticEven.lean):
  ```
  genus (HyperellipticEvenProj H) = H.f.natDegree / 2 - 1
  ```
* `genus_HyperellipticOdd_eq` in
  [`Jacobians/Extensions/Hyperelliptic.lean`](../Jacobians/Extensions/Hyperelliptic.lean):
  ```
  genus (HyperellipticOdd H h) = (H.f.natDegree - 1) / 2
  ```

Both are currently `sorry`. The discharge plan below applies in
parallel to both parities; per-step work is largely shared via the
`reverseData` definitional shortcut for `HyperellipticAffineInfinity`.

## Strategy

The framework approach: build a reusable
`hyperellipticForm (g : Polynomial ℂ) : HolomorphicOneForm X`
constructor in
[`Jacobians/ProjectiveCurve/Hyperelliptic/Form.lean`](../Jacobians/ProjectiveCurve/Hyperelliptic/Form.lean).
Once it lands with linearity + injectivity-on-low-degree, the genus
formula reduces to `LinearIndependent` of `{ hyperellipticForm (X^k) }`
plus the Riemann-Roch upper bound — total ~30 LOC for the headline
theorem.

## Sub-tasks (with current status)

### S1. Affine projX coefficient + analyticity

**File:**
[`Jacobians/ProjectiveCurve/Hyperelliptic/AffineForm.lean`](../Jacobians/ProjectiveCurve/Hyperelliptic/AffineForm.lean)

**Status:** def + linearity (3 lemmas) **DONE** (commit `b2ae9f9`).
Analyticity helper `squareLocalHomeomorph_symm_ne_zero` is `sorry`.

**Remaining:** Prove `squareLocalHomeomorph_symm_ne_zero` (chart-source
⊆ smoothLocusY argument), then prove
`affineProjXCoeff_analyticOn_chartTarget` via composition of
analyticity facts.

**Estimate:** ~50–100 LOC.

### S2. Affine projY coefficient + analyticity (mirror of S1)

**File:** to add to
[`Jacobians/ProjectiveCurve/Hyperelliptic/AffineForm.lean`](../Jacobians/ProjectiveCurve/Hyperelliptic/AffineForm.lean)
or new sibling.

**Status:** Not started.

**Mirror of S1:** `affineProjYCoeff` formula `2 g(x(z)) / f'(x(z))`
where `x(z)` is via `polynomialLocalHomeomorph`.

**Estimate:** ~150 LOC.

### S3. Affine cocycle compatibility on chart overlaps

**Status:** Not started.

**Content:** Proves that the chart-local coefficient transforms
correctly across affine-affine chart overlaps:
* projX × projX: identity transition (both project to x).
* projX × projY: `g(x)/y = 2g(x(y))/f'(x(y)) · f'(x)/(2y)` (chain rule).
* projY × projX: symmetric.
* projY × projY: identity transition (both project to y).

**Reuses Codex's** `affineChartAt_compat` machinery — this is
chart-side compatibility rather than form-side, but the chain-rule
factor that absorbs the change of variable is the same.

**Estimate:** ~150–200 LOC.

### S4. Affine-infinity extension via `reverseData`

**Status:** Not started.

**Content:** S1–S3 transferred to `HyperellipticAffineInfinity` via
the EA1 definitional equality `HyperellipticAffineInfinity H ≡
HyperellipticAffine (reverseData H h)`. Should be ~5 LOC of
`change` + reuse.

**Estimate:** ~50 LOC.

### S5. Cross-summand cocycle (discharges EA2 axioms)

**Files:**
[`Jacobians/ProjectiveCurve/Hyperelliptic/EvenAtlas.lean`](../Jacobians/ProjectiveCurve/Hyperelliptic/EvenAtlas.lean)
(2 axioms `affineLiftChart_compat_infinityLiftChart` and the symmetric).

**Status:** Currently `axiom`. To convert to `theorem`.

**Content:** Möbius transition `x ↦ 1/x` on the gluing region for
projX-projX cross. Three other sub-cases (projX-projY, projY-projX,
projY-projY) involve polynomial corrections.

**Estimate:** ~200–400 LOC across 4 sub-cases.

### S6. Form-level linearity (`Form.lean` sorries)

**Status:** All 4 sorries open (`hyperellipticForm`,
`hyperellipticForm_add`, `hyperellipticForm_smul`,
`hyperellipticForm_zero`).

**Content:** With S1–S5 done, the form is `coeff = case-split on
charts using affineProjXCoeff/affineProjYCoeff/their reverseData
transfers`. Linearity is pointwise from S1's linearity lemmas.

**Estimate:** ~100 LOC.

### S7. Linear independence

**Status:** `sorry` in `Form.lean`.

**Content:** `hyperellipticForm_injOn_lowDegree` then
`hyperellipticForm_linearIndependent` via
`Polynomial.linearIndependent_pow` (Mathlib).

Non-vanishing of `hyperellipticForm g` for nonzero `g` of degree
`< g_topology` follows from the affine projX coefficient being
`g(z)/y(z)` — which has a pole or zero on the curve unless `g = 0`
on the whole chart, which would contradict `g ≠ 0` for polynomials
of bounded degree.

**Estimate:** ~100–200 LOC.

### S8. Riemann–Roch upper bound + headline theorem

**File:** complete the sorries in
[`Jacobians/Extensions/HyperellipticEven.lean`](../Jacobians/Extensions/HyperellipticEven.lean)
and
[`Jacobians/Extensions/Hyperelliptic.lean`](../Jacobians/Extensions/Hyperelliptic.lean).

**Status:** Open.

**Content:** Apply `AX_RiemannRoch` to the canonical divisor:
`dim H⁰(K) - dim H¹(K) = deg K + 1 - g`. With `deg K = 2g - 2`,
`dim H¹(K) = dim H⁰(O) = 1` (Serre duality + connectedness),
`dim H⁰(K) = dim H⁰(Ω¹) = genus`, gives `genus = g`.

Requires setting up the canonical divisor and identifying
`H⁰(K) ≅ HolomorphicOneForm`. Substantial side machinery.

Alternative if canonical-divisor setup is too much: use
`AX_FiniteDimOneForms` directly and rely on the lower bound from
S7 + a separate "finrank exactly equals g" axiom for the upper
bound. Less satisfying but unblocks the genus theorem.

**Estimate:** ~150 LOC for the canonical-divisor version, ~30 LOC
for the direct-axiom version.

## Total estimate

**~800–1500 LOC of substantive proof work**, multi-session.

## Discharge order

Recommended: S1 (foundation) → S2 (mirror) → S3 (cocycle) → S4
(reverseData transfer, free) → S5 (the harder cross-summand) → S6
(form-level linearity) → S7 (linear independence) → S8 (RR + theorem).

Each step is a clean commit. S1, S2, S6, S7 are largely mechanical.
S3 and S5 are the genuinely harder pieces.

## Currently in flight (commit `b2ae9f9`)

S1 partial — affine projX coefficient def + linearity (3 lemmas)
done; analyticity helper `squareLocalHomeomorph_symm_ne_zero` is
sorry. Working on closing this in the next commits.
