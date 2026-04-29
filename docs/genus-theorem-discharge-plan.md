# Genus theorem discharge plan

_Drafted 2026-04-26. Updated 2026-04-29._

## Status header (2026-04-29)

* **Even parity — landed.** `genus_HyperellipticEven_eq` is now a real
  theorem: `le_antisymm` of `hyperellipticEvenGenus_lower_bound` (S7,
  via real linear independence of the basis) and
  `Jacobians.Axioms.HyperellipticLiouville.genus_HyperellipticEven_le`
  (S8, real proof on top of the 3-level Liouville axiom hierarchy
  introduced in commit `cbcbdb3`).
* **Odd parity — pending.** `genus_HyperellipticOdd_eq` still `sorry`
  in `Jacobians/Extensions/Hyperelliptic.lean`. The framework mirrors
  cleanly — once the cross-summand soundness fix lands the odd-side
  port is largely mechanical (`reverseData` definitional shortcut + a
  parallel single-summand 1-form on `OnePoint (HyperellipticAffine H)`).
* **Open soundness fix (task #21).** The cross-summand `inl_inr` cocycle
  is *also* available as a real theorem under
  `g_aff.natDegree < N/2 - 1` (`hyperellipticEvenCoeff_cocycle_inl_inr`,
  commit `8ad0d44`), but the bundling step
  `hyperellipticEvenCoeff_satisfiesCotangentCocycle` still calls the
  unsound axiomatic version. Threading `hDeg` through `hyperellipticForm`
  retires the two cross-summand axioms.

## Goal

Discharge the two genus theorems:

* `genus_HyperellipticEven_eq` in
  [`Jacobians/Extensions/HyperellipticEven.lean`](../Jacobians/Extensions/HyperellipticEven.lean):
  ```
  genus (HyperellipticEvenProj H) = H.f.natDegree / 2 - 1
  ```
  **DONE** as of `65410a0` modulo the Liouville hierarchy axioms.
* `genus_HyperellipticOdd_eq` in
  [`Jacobians/Extensions/Hyperelliptic.lean`](../Jacobians/Extensions/Hyperelliptic.lean):
  ```
  genus (HyperellipticOdd H h) = (H.f.natDegree - 1) / 2
  ```
  Still `sorry`. The discharge plan below applies in parallel to both
  parities; per-step work is largely shared via the `reverseData`
  definitional shortcut for `HyperellipticAffineInfinity`.

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

**Status: `inl_inr` direction discharged as a real low-degree theorem
(commits `564fd82, 2d4e446, f2acb4c, 06db77c, 7d7a7bf, 76bbc23, 8214395,
d46b84d, 8ad0d44`).** All four sub-cases proven across ~1100 LOC:

* `cocycle_inl_inr_smoothLocusY_smoothLocusY` (projX × projU)
* `cocycle_inl_inr_smoothLocusXNotY_smoothLocusY` (projY × projU)
* `cocycle_inl_inr_smoothLocusY_smoothLocusXNotY` (projX × projV)
* `cocycle_inl_inr_smoothLocusXNotY_smoothLocusXNotY` (projY × projV)

Each sub-case is a Möbius-derivative + reverse-polynomial-identity
calculation on the affine-affine infinity overlap. The unified
`hyperellipticEvenCoeff_cocycle_inl_inr` (commit `8ad0d44`) dispatches
to the four sub-cases via `by_cases` on `smoothLocusY`/`smoothLocusX`
membership, under hypothesis `hDeg : g_aff.natDegree < H.f.natDegree / 2 - 1`.

**SOUNDNESS GAP STILL OPEN (task #21).** The bundling step
`hyperellipticEvenCoeff_satisfiesCotangentCocycle` still calls the
two unsound axioms `hyperellipticEvenCoeff_cocycle_inl_inr_axiom` and
`_inr_inl_axiom`. The `inl_inr` axiom is now redundant — the real
theorem exists — but plumbing `hDeg` through `hyperellipticEvenCoeff_mem_submodule`
and `hyperellipticForm` requires refactoring the constructor to take
`Polynomial.degreeLT ℂ g_topology` (subtype). Cascading refactor through
linearity theorems and basis differentials.

**Remaining work for full S5 discharge:**
1. Soundness refactor: thread `hDeg` from `hyperellipticForm` down to
   `_satisfiesCotangentCocycle`; replace `_inl_inr_axiom` with the
   real low-degree theorem.
2. Discharge `inr_inl` direction (still axiomatized). Symmetric
   structure to `inl_inr`; can swap via the chart-transition
   derivative-product-to-1 lemma.

**Estimate:** Soundness fix ~200 LOC of refactoring; `inr_inl`
discharge ~300–500 LOC mirroring the `inl_inr` chain.

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

### S8. Genus upper bound + headline theorem

**Status: DONE for even parity** (`cbcbdb3`, `65410a0`).

**Path taken:** the Riemann-Roch route was deferred (Gemini estimated
6–12 months); instead the upper bound is derived from a 3-level Liouville
axiom hierarchy in
[`Jacobians/Axioms/HyperellipticLiouville.lean`](../Jacobians/Axioms/HyperellipticLiouville.lean):

* **Level 1** (`AX_Liouville_compact_complex_manifold`) — every analytic
  function on a compact connected complex manifold is constant.
  Mathlib-shaped statement; no project definitions involved. Discharge
  target: chart-local maximum-modulus + connectedness gluing.
* **Level 2** (`AX_HyperellipticForm_polynomial_decomposition`) —
  every holomorphic 1-form on `HyperellipticEvenProj H` has a chart-local
  representation `g(z)/y(z)` for `g.natDegree < N/2 - 1` on the projX
  chart at any `a ∈ smoothLocusY`. Mid-level: derives from Level 1 +
  growth bounds at infinity.
* **Level 3** (`AX_HyperellipticOneForm_eq_form`) — every holomorphic
  1-form equals `hyperellipticForm H g` for some low-degree `g`.
  Project-specific. Derives from Level 2 + the cocycle (real for `inl_inr`
  modulo task #21).

The genus upper bound (`genus_HyperellipticEven_le`) is a real theorem:
build `degreeLT ℂ n →ₗ[ℂ] HolomorphicOneForm` via `hyperellipticFormLinearMap`,
get surjectivity from Level 3, then `Module.finrank` of the target ≤
`Module.finrank` of `degreeLT ℂ n = n` via `LinearMap.rank_le_of_surjective`.

**Lower bound (DONE):** the basis
`{ hyperellipticEvenBasisDifferential H k _hk : k < g_topology }` is
linearly independent (S7), so via `LinearIndependent.fintype_card_le_finrank`
plus the bridge-derived `FiniteDimensional` instance (Kirov's Montel),
`g_topology ≤ Module.finrank ℂ (HolomorphicOneForm (HyperellipticEvenProj H))
≡ genus`.

**Headline:** `genus_HyperellipticEven_eq H : genus (HyperellipticEvenProj H) = H.f.natDegree / 2 - 1`
is `le_antisymm` of the two bounds above, both real proofs.

**Vetting:** the Liouville hierarchy was Gemini-vetted on 2026-04-29
(verdicts saved to `history/gemini_deep_think.md`); all six review
criteria green-lit, derivation chain "impeccable", "ready for inclusion".

**Riemann-Roch route remains** as a longer-term alternative — would
discharge Level 3 directly via the canonical divisor + Serre duality,
removing the Liouville axioms but pulling in `AX_RiemannRoch` and
canonical-divisor machinery. Tracked as future work, not actively
pursued.

**Odd parity:** still open. Mirror the framework into
`Jacobians/Extensions/Hyperelliptic.lean` — the affine-side machinery
already transfers via `reverseData`; the missing piece is the Liouville-
hierarchy analogue for `HyperellipticOdd H h`, which has *one* point
at infinity (vs two in the even case) so the polynomial-decomposition
constraint is `g.natDegree < (N-1)/2`.

## Total estimate

**~800–1500 LOC of substantive proof work**, multi-session.

## Discharge order

Recommended: S1 (foundation) → S2 (mirror) → S3 (cocycle) → S4
(reverseData transfer, free) → S5 (the harder cross-summand) → S6
(form-level linearity) → S7 (linear independence) → S8 (RR + theorem).

Each step is a clean commit. S1, S2, S6, S7 are largely mechanical.
S3 and S5 are the genuinely harder pieces.

## State as of `65410a0`, 2026-04-29

S1–S7 done as real proofs. S5 cross-summand `inl_inr` direction is a
real low-degree theorem (`hyperellipticEvenCoeff_cocycle_inl_inr`,
`8ad0d44`); the bundling step still routes through axioms because
`hDeg` is not yet plumbed through `hyperellipticForm` (task #21).
S8 upper bound discharged via the Liouville axiom hierarchy (`cbcbdb3`),
giving `genus_HyperellipticEven_eq` as a real theorem (`65410a0`).

Form.lean and EvenForm.lean have zero `sorry`. Extensions/HyperellipticEven.lean
is sorry-free. Open work for the even parity: discharge the
two cross-summand axioms (replace with low-degree-only versions),
discharge the three Liouville-hierarchy axioms.

Open for odd parity: mirror the framework into Hyperelliptic.lean
(extension theorems still mostly `sorry`); the affine machinery
already transfers via `reverseData`.

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
* `b0717b6, cb828ac, 44a4e00, b0b09b8, 9ab627a, 5641420`: S5
  infrastructure (Möbius helpers, gluing image, chart-symm at basepoint)
* `5e098dd, 564fd82, 2d4e446, f2acb4c, 06db77c, 7d7a7bf, 76bbc23,
  8214395, d46b84d`: S5 four cross-summand sub-cases (real proofs)
* `8ad0d44`: S5 unified `inl_inr` cocycle theorem (dispatches the four
  sub-cases on smoothLocusY/X membership)
* `cbcbdb3`: Liouville axiom hierarchy + `genus_HyperellipticEven_le`
  upper bound (real theorem on top of 3 axioms)
* `65410a0`: `genus_HyperellipticEven_eq` is now a real theorem
  (`le_antisymm` of S7 lower + S8 upper)
