# Chart-transfer layer — `affCoeff` (Gemini-deep-think-vetted, Approach A)

*2026-06-07. MRD greenlit "build the chart-transfer layer". This is the M0-level
foundation that unblocks hAna (and hence the whole green anti-invariance
superstructure) past the `Quotient.out` representative gap.*

## The gap (recap)
`form.coeff (mk inl a)` is analytic only in `extChartAt (mk inl a)` = the
`Quotient.out` chart. The setoid glues `(x,y)↔(1/x,…)` for all `x≠0`, so for
`x≠0` `Quotient.out (mk inl a)` may be the ∞ rep ⇒ `form.coeff (mk inl a)` lives
in the `u=1/x` coordinate, and no point of X has the affine x-chart as its
`chartAt`. So the point-keyed cocycle can't reach the affine chart, and the
projX-analyticity lemmas (gated on `Quotient.out q = inl a`) only fire at `x=0`.

## The fix — `affCoeff` (Approach A, decisively per Gemini)
ω's coefficient in the affine x-chart at `a`, independent of `Quotient.out`:
```lean
noncomputable def affCoeff (form : HolomorphicOneForm (HyperellipticEvenProj H))
    (a : HyperellipticAffine H) : ℂ → ℂ :=
  match Quotient.out (Quotient.mk _ (Sum.inl a)) with
  | Sum.inl _ => form.coeff (Quotient.mk _ (Sum.inl a))
  | Sum.inr _ => fun z => form.coeff (Quotient.mk _ (Sum.inl a)) (1 / z) * (-1 / z ^ 2)
```
Only ONE gluing transition (`u=1/x`, `du = −dx/x²`), so this stays in elementary
1D complex analysis — NO manifold/atlas/`ContMDiffGroupoid` machinery, NO cocycle.

## Analyticity — `AnalyticOn ℂ (affCoeff form a) (affineChartProjX a hpY).target`
Needs ONLY Field 1 (`form.2.1`, chartAt analyticity) + the explicit transition.
- **`inl` branch:** `affCoeff = form.coeff (mk inl a)`; chartAt IS the affine chart
  (Quotient.out = inl a) ⇒ exactly the existing `form_coeff_analyticOn_affineProjX_target`.
- **`inr` branch** (the new content), on `target ∩ {z≠0}`:
  `affCoeff z = form.coeff (mk inl a) (1/z) · (−1/z²)`.
  1. `z↦1/z` analytic on `{z≠0}` (`AnalyticOn.inv`/`.div`); `z↦−1/z²` analytic (`.inv`,`.pow`,`.const_mul`).
  2. `form.coeff (mk inl a)` analytic on `(extChartAt (mk inl a)).target` = ∞ target (Field 1).
  3. domain mapping: `z ∈ affine target ∩{z≠0} ⇒ 1/z ∈ ∞ target` (from the gluing API).
  4. `AnalyticOn.comp` + `AnalyticOn.mul`.
  (At a branch point `f z=0`, `z≠0` since `f 0 ≠ 0`… or handle x=0 in the inl branch
  / the branch points are away from x=0 generically — confirm `affineChartProjX` target
  for the inr-branch points excludes 0, or restrict to {z≠0} and treat x=0 via inl.)

## Retrofit (reuse the GREEN superstructure, don't rebuild)
REDEFINE `liouvilleProjXNumerator`/`liouvilleLocalSheetSum`/`liouvilleTwoSheetSum`
to use `affCoeff form a` in place of `form.coeff (proj inl a)`.
- `affCoeff_of_inl` (when `Quotient.out (mk inl a)=inl a`, e.g. x=0 witness):
  `affCoeff form a = form.coeff (mk inl a)` — one `rw`, so the x=0 / branch-point
  local proofs (removable singularity in the w-chart) go through unchanged.
- hAna becomes provable for ALL x via `affCoeff` analyticity above.
- hBranch / h0 / the Liouville capstone are UNCHANGED (they consume the global
  `liouvilleTwoSheetSum`, now `affCoeff`-based).

## ⚠ Correction to Gemini point 4
Gemini suggested proving `affCoeff form a.invol = −affCoeff form a` from the
cross-summand cocycle to "shield the superstructure". That is WRONG: σ-anti-invariance
is a GLOBAL theorem (the +1 eigenspace H⁰(ℙ¹,Ω)=0); local cocycle data cannot yield
the −1 eigenvalue. Anti-invariance still comes from the **green Liouville scaffolding**
(two-sheet sum ≡ 0 via removable-sing + Liouville). `affCoeff`'s ONLY role is making
hAna (off-root analyticity) hold for all x. Do NOT try to derive anti-invariance from
the cocycle.

## KEY: the axiom is `hQ`-guarded (discovered 2026-06-07)
`AX_HyperellipticForm_polynomial_decomposition` quantifies over
`(a, hpY, q, hQ : Quotient.out q = Sum.inl a, z ∈ affine target)` and constrains
`form.coeff q z`. The `hQ` guard means it ONLY constrains affine-rep points, where
`form.coeff q = affCoeff form a` (the `inl` branch). So the discharge: build the
global numerator `G z := affCoeff form (chosen a at z) z · √f(z)`, prove it's a
polynomial `g` (entire via affCoeff analyticity + anti-invariance + removable +
Liouville-growth), then at `hQ` points `form.coeff q z = affCoeff form a z = G z/√f
= g.eval z/√f` via `affCoeff_of_inl`. NO need to handle `form.coeff` at ∞-rep
points. The CHOSEN-point trick: `liouvilleChosenAffinePoint z` has `a.val.1 = z`
AND `a.invol.val.1 = z` (invol negates only y), so BOTH `affCoeff form a` and
`affCoeff form a.invol` are analytic at the common basepoint `z`
(`affCoeff_analyticAt_basepoint`) ⇒ hAna is DIRECT after the retrofit.

## Sub-tasks
- **CT-2** ✅ DONE: `affCoeff_analyticAt_basepoint : AnalyticAt ℂ (affCoeff form a) a.val.1` (2df253e), + `affCoeff`/`affCoeff_of_inl`/`affCoeff_analyticOn_of_inl` + center helpers.
1. **CT-1** define `affCoeff` + `affCoeff_of_inl` reduction lemma. ✅ DONE.
2. **CT-2** `affCoeff` analyticity on the affine target (inl branch trivial; inr branch
   via 1/z transition + Field 1 + domain mapping). The real new work.
3. **CT-3** retrofit `liouvilleProjXNumerator`/`liouvilleTwoSheetSum` to `affCoeff`;
   fix downstream rewrites; rebuild green.
4. **CT-4** discharge hAna (now provable) + hBranch (DR-B w-cancellation) + h0 (DR-C) ⇒
   anti-invariance ⇒ P1 ⇒ flip L2 axiom ⇒ L3 ⇒ 56.
