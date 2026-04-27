# S5 cross-summand cocycle discharge — architecture and remaining work

_Drafted 2026-04-27 (continuing from autonomous-loop session). Captures
the current state of the S5 work and the precise remaining steps to
replace the cross-summand cocycle axioms with real proofs._

## Goal

Replace the two cross-summand cocycle axioms in `EvenForm.lean`
(`hyperellipticEvenCoeff_cocycle_inl_inr_axiom` and `_inr_inl_axiom`) with
real proofs, valid for low-degree polynomials `g_aff` (degree
`< g_topology - 1`).

## What's already real

All in `Jacobians/ProjectiveCurve/Hyperelliptic/EvenForm.lean`:

### Polynomial / algebraic core
* `reflect_eval_inv_mul_pow` — `(reflect N p).eval (x⁻¹) * x^N = p.eval x`
  for `p.natDegree ≤ N`, `x ≠ 0`.
* `eval_eq_neg_infReverse_eval_inv_mul_pow` — the gluing identity:
  `g.eval x = -(infReverse H g).eval (x⁻¹) * x ^ (H.f.natDegree / 2 - 2)`
  for low-degree `g` and nonzero `x`.

### Möbius derivative
* `hasDerivAt_inv_complex` — `HasDerivAt (z ↦ z⁻¹) (-(z²)⁻¹) z` for
  nonzero `z`.
* `fderiv_inv_apply_one` — `fderiv ℂ (z ↦ z⁻¹) z 1 = -(z²)⁻¹`.

### Gluing-image construction
* `affineGluingImage a hxNZ` — `(1/x, y · x⁻¹^(g+1))` as a
  `HyperellipticAffineInfinity H` point, valid when `a.val.1 ≠ 0`.
* `affineGluingImage_val_fst/snd` — coordinate values.
* `hyperellipticEvenGlue_affineGluingImage` — the gluing relation holds.
* `proj_eq_affineGluingImage` — `Quotient.mk (Sum.inl a) = Quotient.mk
  (Sum.inr (affineGluingImage a hxNZ))`.
* `affineGluingImage_mem_smoothLocusY` — gluing image of a smoothLocusY
  point is in smoothLocusY of the reversed data.

### Coordinate-level cocycle (the algebraic core, real proof)
* `cross_summand_cocycle_coord` — for low-degree `g_aff` and coordinates
  `(z, y, v)` satisfying the gluing relation `v = y · z⁻¹^(g+1)`,
  the cocycle equation `g_aff(z)/y = (infReverse H g_aff)(z⁻¹)/v · (-(z²)⁻¹)`
  follows from the polynomial identity. Free of chart structure.

### Chart-symm identification
* `squareLocalHomeomorph_symm_at_basepoint` — at the basepoint,
  `e_a.symm (H.f.eval a.val.1) = a.val.2`.
* `proj_inl_eq_proj_inr_iff` — projection equality forces `b` to be the
  gluing image of `a`.

## What's needed for the chart-level cocycle

Two structural pieces and one final assembly:

### 1. Chart-symm consistency in a neighborhood (analytic continuation)

**Statement:** For `a ∈ smoothLocusY` with `a.val.1 ≠ 0` and `b :=
affineGluingImage a hxNZ`, and `z` in some chart-overlap neighborhood
of `a.val.1`:
```
e_a.symm (H.f.eval z) · z⁻¹^(g+1) = e_b.symm ((H.f.reverse).eval z⁻¹)
```

**Why it's hard:** At each `z`, both sides square to the same value
`(H.f.reverse).eval z⁻¹`, so they're equal up to sign. Picking the
correct sign requires continuity from the basepoint, where they agree
(both equal `b.val.2`).

**Approach:** Connectedness argument. Define `f(z) := e_a.symm (H.f.eval z)
· z⁻¹^(g+1) - e_b.symm ((H.f.reverse).eval z⁻¹)`. Then `f` is continuous,
`f(a.val.1) = 0`, and `f² · (sum of two branches) = 0`. The "sum of
branches" is bounded away from zero near the basepoint, forcing `f = 0`
on a neighborhood.

**Estimated effort:** 100-200 LOC. Requires careful neighborhood / open
ball reasoning, plus understanding of `IsOpen` in the IFT chart targets.

### 2. Lift coordinate cocycle to chart level

**Statement:** Discharge the cross-summand axiom
`hyperellipticEvenCoeff_cocycle_inl_inr_axiom` (and the symmetric one).

**Approach:**
1. From `hQ : Quotient.out q = Sum.inl a` and `hQ' : Quotient.out q' =
   Sum.inr b`, identify `chart_q = affineLiftChart H _ a` and
   `chart_q' = infinityLiftChart H _ b`.
2. From `hz : z ∈ chart_q.target` and `hSrc : chart_q.symm z ∈
   chart_q'.source`, unwind via `lift_openEmbedding_target/source`:
   `z ∈ affineChartAt a .target` and the affine point
   `affineChartAt a .symm z` (which we know has x-coord `z` in projX
   case) is gluing-related to some infinity point in `chart_b.source`.
3. By `proj_inl_eq_proj_inr_iff` applied to the projection-equality
   from gluing, the infinity point is `affineGluingImage (chart_a.symm z)
   (hxNZ)` for some `hxNZ` derived from `hSrc`.
4. By `lift_openEmbedding_apply`, `chart_q' (chart_q.symm z) =
   affineChartAt (reverseData) b applied to the gluing image`.
   In the projU case, this evaluates to the gluing image's u-coord = `z⁻¹`.
5. By `Filter.EventuallyEq.fderiv_eq`, `fderiv (chart_q' ∘ chart_q.symm)
   z 1 = fderiv (z ↦ z⁻¹) z 1 = -(z²)⁻¹` (using `fderiv_inv_apply_one`).
6. Apply `cross_summand_cocycle_coord` with `(z, y, v) = (z,
   e_a.symm (H.f.eval z), e_b.symm ((H.f.reverse).eval z⁻¹))`. The
   gluing relation `v = y · z⁻¹^(g+1)` follows from step 1 above.

**Estimated effort:** 200-400 LOC. Lots of structural unwinding.

### 3. Mirror axiom (`_inr_inl`)

**Approach:** Symmetric to step 2, swapping affine/infinity roles. Or
derive from the inl_inr cocycle plus symmetry of `SatisfiesCotangentCocycle`.

**Estimated effort:** 100 LOC if mostly mirror, 200 if from scratch.

## Total estimate

* Step 1 (analytic continuation): 100-200 LOC
* Step 2 (chart-level lift, inl_inr): 200-400 LOC
* Step 3 (mirror, inr_inl): 100-200 LOC

**Total: 400-800 LOC.** Multi-day focused effort. Aligns with Gemini's
1-3 weeks estimate for the full discharge.

## After S5 discharge

* The two `axiom`s in `EvenForm.lean` become real `theorem`s.
* `hyperellipticForm` for low-degree `g` produces a genuinely
  holomorphic 1-form (no soundness gap).
* The S8 upper bound becomes attackable: any global holomorphic 1-form
  must equal `hyperellipticForm H g` for some low-degree `g` (by a
  Liouville/maximum-principle argument). This gives `genus ≤
  g_topology` directly, sidestepping the full Riemann-Roch
  infrastructure.
