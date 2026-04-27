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

**Status: DONE** (`a525b4d`, `1f75707`). Def + linearity + analyticity
on the chart target. The `squareLocalHomeomorph_symm_ne_zero` helper
discharged via the narrow IFT axiom
`squareLocalHomeomorph_zero_notMem_source`.

### S2. Affine projY coefficient + analyticity (mirror of S1)

**File:**
[`Jacobians/ProjectiveCurve/Hyperelliptic/AffineForm.lean`](../Jacobians/ProjectiveCurve/Hyperelliptic/AffineForm.lean).

**Status: DONE** (`689b602`). `affineProjYCoeff` def + linearity +
analyticity on the chart target landed via the mirror of S1, with the
narrow IFT axiom `polynomialLocalHomeomorph_no_critical_in_source` for
the structural piece.

### S3. Affine cocycle compatibility on chart overlaps

**Status: DONE** (`ad554ee`, `e28c7ac`, `25286be`, `6fe2a18`).

All four sub-cases assembled in
[`AffineForm.lean`](../Jacobians/ProjectiveCurve/Hyperelliptic/AffineForm.lean):
* projX × projX (`hyperellipticAffineCoeff_cocycle_projX_projX`)
* projY × projY (`hyperellipticAffineCoeff_cocycle_projY_projY`)
* projX × projY (`hyperellipticAffineCoeff_cocycle_projX_projY`,
  chain rule)
* projY × projX (mirror, chain rule)

### S4. Affine-infinity extension via `reverseData`

**Status: DONE** (`1fa766a`). The full affine bundle transferred to
`HyperellipticAffineInfinity` via the EA1 definitional equality, in
[`AffineInfinityForm.lean`](../Jacobians/ProjectiveCurve/Hyperelliptic/AffineInfinityForm.lean).
Sorry-free, axiom-free — pure `change` + reuse.

### S5. Cross-summand cocycle (`EvenForm` Möbius axioms)

**Files:**
[`EvenForm.lean`](../Jacobians/ProjectiveCurve/Hyperelliptic/EvenForm.lean).

**Status: scaffolded with sound hypothesis** (`ea35935`, post-Gemini
review). The two cross-summand cocycle axioms now take the gluing
relation `g_inf = infReverse H g_aff` as an **explicit hypothesis**
rather than quantifying over arbitrary pairs (the latter was unsound:
the cocycle equation only holds for the Möbius-paired infinity-side
polynomial).

**Content:** Möbius transition `x ↦ 1/x` on the gluing region.
Discharging the axioms requires explicit chain-rule computations on
the polynomial corrections.

**Estimate:** ~200–400 LOC across the 4 sub-cases. Currently
axiomatized; the soundness fix means the axioms are no longer false.

### S6. Form-level constructor + linearity (`Form.lean`)

**Status: DONE** (`d07b9bc`, `337f569`). The constructor
`hyperellipticForm` is real (composes `hyperellipticEvenCoeff` with
the bundled-cocycle membership proof from
[`EvenForm.lean`](../Jacobians/ProjectiveCurve/Hyperelliptic/EvenForm.lean)).
Linearity (`_add`, `_smul`, `_zero`, packaged
`hyperellipticFormLinearMap`) is sorry-free, derived from the
within-summand linearity lemmas + `infReverse_add` / `infReverse_smul`.

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

## Currently in flight (as of `337f569`, 2026-04-26)

S1–S4 are done as real proofs. S5 cross-summand cocycles are
axiomatized but with the soundness hypothesis fix (`ea35935`,
post-Gemini deep-think review). S6 — `hyperellipticForm` constructor
and linearity — is sorry-free. S7 (linear independence) and S8
(Riemann–Roch upper bound) are the remaining pieces.

Form.lean current sorry inventory: 3 (down from 8 at the original
scaffold).
