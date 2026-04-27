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

**Status: scaffolded with partial soundness fix** (`ea35935`,
post-Gemini review #1). The two cross-summand cocycle axioms now take
the gluing relation `g_inf = infReverse H g_aff` as an **explicit
hypothesis** rather than quantifying over arbitrary pairs (the latter
was unsound: the cocycle equation only holds for the Möbius-paired
infinity-side polynomial).

**KNOWN SOUNDNESS GAP** (Gemini review #2,
`docs/gemini-review-genus-framework.md`, §B with Claude's correction):
the axioms are still mathematically false for `g_aff.natDegree ≥
H.f.natDegree / 2 - 1` (form has poles at infinity, cocycle equation
literally fails). Hard to exploit due to non-computable `Quotient.out`,
but a real liability.

**Recommended fix:** Add `(hDeg : g_aff.natDegree < H.f.natDegree / 2 - 1)`
to both axioms; refactor `hyperellipticForm` to take `Polynomial.degreeLT
ℂ g_topology` (subtype) so the LinearMap structure is preserved. Cascading
refactor through linearity theorems and basis differentials. Tracked as
task #21.

**Content (long-term):** Möbius transition `x ↦ 1/x` on the gluing region.
Discharging the axioms (replacing them with real proofs for the constrained
domain) requires explicit chain-rule computations on the polynomial
corrections.

**Estimate:** Soundness fix ~200 LOC of refactoring. Real discharge of
the axioms ~200–400 LOC of new proof per Gemini's 1-3 weeks estimate.

### S6. Form-level constructor + linearity (`Form.lean`)

**Status: DONE** (`d07b9bc`, `337f569`). The constructor
`hyperellipticForm` is real (composes `hyperellipticEvenCoeff` with
the bundled-cocycle membership proof from
[`EvenForm.lean`](../Jacobians/ProjectiveCurve/Hyperelliptic/EvenForm.lean)).
Linearity (`_add`, `_smul`, `_zero`, packaged
`hyperellipticFormLinearMap`) is sorry-free, derived from the
within-summand linearity lemmas + `infReverse_add` / `infReverse_smul`.

### S7. Linear independence

**Status: DONE** (`74266e2`). Form.lean is now sorry-free for the
linear-independence chain:

* `hyperellipticAffineCoeff_injective_at_smoothLocusY/_smoothLocusX`
  — affine-side polynomial recovery via the chart-local coefficient
  `g(z)/y(z)` (or `2g(x(z))/f'(x(z))`) on the chart target (an open
  non-empty subset of ℂ, hence infinite). Polynomial identity finishes.
* `hyperellipticForm_eq_of_agree_at_affine_smoothY/_smoothX` —
  conditional form-level injectivity at a quotient point with
  `Quotient.out q = Sum.inl a`.
* `quotient_out_of_zero_x` — for affine `a₀` with `a₀.val.1 = 0`,
  `Quotient.out (Quotient.mk _ (Sum.inl a₀)) = Sum.inl a₀` because
  the gluing graph isolates such points (gluing requires `x ≠ 0`).
* `witnessZeroX H` — natural witness `(0, ±√H.f(0))`. Case-split:
  - `H.f(0) ≠ 0`: in `smoothLocusY`.
  - `H.f(0) = 0`: in `smoothLocusX` (squarefree ⇒ `f'(0) ≠ 0`).
* `hyperellipticForm_injective` — unconditional injectivity.
* `hyperellipticForm_injOn_lowDegree` — corollary.
* `hyperellipticForm_linearIndependent` — via
  `Polynomial.basisMonomials` + `LinearMap.linearIndependent_iff`.

Cross-references: `b384a12` discharges `hyperellipticEvenDxOverY`,
`hyperellipticEvenBasisDifferential`, and
`hyperellipticEvenBasisDifferential_linearIndependent` in
`Extensions/HyperellipticEven.lean`. `95f22fa` adds
`hyperellipticEvenGenus_lower_bound` (`g_topology ≤ genus`).

### S8. Riemann–Roch upper bound + headline theorem

**Status: lower bound DONE** (`95f22fa`,
`hyperellipticEvenGenus_lower_bound`); upper bound still open.

**File:** the remaining sorry is `genus_HyperellipticEven_eq` in
[`Jacobians/Extensions/HyperellipticEven.lean`](../Jacobians/Extensions/HyperellipticEven.lean)
(and the analogous `genus_HyperellipticOdd_eq` in
[`Hyperelliptic.lean`](../Jacobians/Extensions/Hyperelliptic.lean)).

**Lower bound (DONE):** the basis
`{ hyperellipticEvenBasisDifferential H k _hk : k < g_topology }` is
linearly independent (S7), so via `LinearIndependent.fintype_card_le_finrank`
plus the bridge-derived `FiniteDimensional` instance,
`g_topology ≤ Module.finrank ℂ (HolomorphicOneForm (HyperellipticEvenProj H))
≡ genus`.

**Upper bound (TODO):** Apply `AX_RiemannRoch` to the canonical divisor:
`dim H⁰(K) - dim H¹(K) = deg K + 1 - g`. With `deg K = 2g - 2`,
`dim H¹(K) = dim H⁰(O) = 1` (Serre duality + connectedness),
`dim H⁰(K) = dim H⁰(Ω¹) = genus`, gives `genus = g`.

Requires setting up the canonical divisor and identifying
`H⁰(K) ≅ HolomorphicOneForm`. Substantial side machinery — Gemini
review #2 estimated 6-12 months for this path.

Per Gemini review #2 (E), the **strongly recommended alternative** is
to discharge the cross-summand cocycle (S5) for low-degree polynomials
first. This:
* Eliminates the soundness gap from S5.
* Produces forms that are *truly* holomorphic at infinity.
* Makes the upper bound argument constructive: any global holomorphic
  1-form must be of the form `hyperellipticForm H g` for some low-
  degree `g`, by a Liouville/maximum-principle-style argument on the
  affine chart.

**Estimate:** Cocycle discharge ~1-3 weeks; full Riemann-Roch ~6-12 months.

## Total estimate

**~800–1500 LOC of substantive proof work**, multi-session.

## Discharge order

Recommended: S1 (foundation) → S2 (mirror) → S3 (cocycle) → S4
(reverseData transfer, free) → S5 (the harder cross-summand) → S6
(form-level linearity) → S7 (linear independence) → S8 (RR + theorem).

Each step is a clean commit. S1, S2, S6, S7 are largely mechanical.
S3 and S5 are the genuinely harder pieces.

## Currently in flight (as of `840bc65`, 2026-04-27)

S1–S4 done as real proofs. S5 cross-summand cocycles axiomatized with
the gluing hypothesis (`ea35935`); known soundness gap for high-degree
g_aff (Gemini review #2, task #21). S6 (form constructor + linearity),
S7 (injectivity + linear independence), and the S8 lower bound are
all sorry-free. Only `genus_HyperellipticEven_eq` itself remains
(needs S8 upper bound from RR or — Gemini's preferred path — from
discharging the S5 cocycle for low-degree g).

Form.lean is sorry-free. Extensions/HyperellipticEven.lean has 1 sorry
(`genus_HyperellipticEven_eq`).

### Recent commits chronological

* `a525b4d, 689b602`: S1, S2 (affine projX/projY analyticity)
* `ad554ee, e28c7ac, 25286be, 6fe2a18`: S3 (4 sub-case cocycles)
* `1fa766a`: S4 (affine-infinity transfer)
* `83902d8`: unified `hyperellipticEvenCoeff` family
* `5d18cee, b314e1a`: same-summand cocycles + generic helper
* `10a1957`: bundled cocycle (with original unsound axiom)
* `d07b9bc`: `hyperellipticForm` constructor
* `ea35935`: soundness fix #1 (added `hGluing` hypothesis)
* `337f569`: S6 linearity sorry-free
* `7294e4d, 6cd2143`: S7 affine injectivity helpers
* `e9c48e7`: conditional form-level injectivity
* `74266e2`: S7 complete (injective + linearIndependent)
* `b384a12, 95f22fa`: S8 basis discharges + lower bound
* `7673ef2`: Gemini review #2 doc with soundness analysis
* `5447723`: docstring warning for known soundness gap
* `840bc65`: lint cleanup (omit + drop redundant Fact args)
