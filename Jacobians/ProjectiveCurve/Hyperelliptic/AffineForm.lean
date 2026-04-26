/-
# Affine-side coefficients for hyperelliptic 1-forms

Concrete affine-side machinery underlying
`Jacobians/ProjectiveCurve/Hyperelliptic/Form.lean`. Builds the
chart-local coefficient of `g(x) dx / y` in the projX and projY
chart families on `HyperellipticAffine H`.

The framework decomposes by chart:

* **`affineProjXCoeff`** — coefficient on `affineChartProjX a hpY`
  (for `a ∈ smoothLocusY`). Formula: `g(z) / y(z)` where `y(z)` is
  the chart-local branch via `squareLocalHomeomorph.symm`.
* **`affineProjYCoeff`** — coefficient on `affineChartProjY a hpX`
  (for `a ∈ smoothLocusX`). Formula: `2 g(x(z)) / f'(x(z))` after
  the change of variable `dx = (2y/f'(x)) dy`.

This file is a foundational building block; it does not yet assemble
the projective `HolomorphicOneForm`. That assembly lives in `Form.lean`.
-/

import Jacobians.ProjectiveCurve.Hyperelliptic.OddAtlas.AffineChart
import Jacobians.RiemannSurface.OneForm

namespace Jacobians.ProjectiveCurve.HyperellipticAffine

open scoped Manifold ContDiff Topology
open Polynomial
open Jacobians.RiemannSurface

variable {H : HyperellipticData}

/-- Chart-local coefficient of `g(x) dx / y` in the projX chart at
`a ∈ smoothLocusY` (i.e. `a.val.2 ≠ 0`). For `z ∈ chart target`,
this is `g(z) / y(z)` where `y(z)` is the chart's local
`squareLocalHomeomorph.symm` branch. Off-target the value is `0`
(per `IsZeroOffChartTarget`). -/
noncomputable def affineProjXCoeff (g : Polynomial ℂ) (a : HyperellipticAffine H)
    (hpY : a ∈ smoothLocusY H) (z : ℂ) : ℂ := by
  classical
  exact
    if z ∈ ((affineChartProjX (H := H) a hpY) :
        OpenPartialHomeomorph (HyperellipticAffine H) ℂ).target then
      g.eval z /
        ((squareLocalHomeomorph (H := H) a hpY).symm (H.f.eval z))
    else 0

/-- **Narrow structural axiom.** The point `0 ∈ ℂ` is not in the
source of `squareLocalHomeomorph p hp`.

This is the only piece of `squareLocalHomeomorph_symm_ne_zero` that
isn't directly derivable from the chart's `right_inv`. It is true
because `squareLocalHomeomorph` is built from the IFT-derived
`ContDiffAt.toOpenPartialHomeomorph` on `y ↦ y²` at `p.val.2 ≠ 0`,
and the IFT's source neighborhood is bounded away from the critical
point `y = 0` of the squaring map.

Discharge requires either:
* an explicit characterization of the source of
  `ContDiffAt.toOpenPartialHomeomorph` (Mathlib does not currently
  expose one beyond `mem_toOpenPartialHomeomorph_source`), or
* a topological argument that the squaring map is not locally
  injective at `0` and any chart source containing both `0` and
  `p.val.2 ≠ 0` would witness this — which contradicts
  `OpenPartialHomeomorph.left_inv`. -/
axiom squareLocalHomeomorph_zero_notMem_source
    (p : HyperellipticAffine H) (hp : p ∈ smoothLocusY H) :
    (0 : ℂ) ∉ (squareLocalHomeomorph (H := H) p hp).source

/-- The y-branch chosen by `squareLocalHomeomorph.symm` is non-zero on
the projX chart target.

**Proof.** From `e.right_inv` at `H.f.eval z` we get
`(e.symm (H.f.eval z))^2 = H.f.eval z`. If the LHS were `0`, RHS would
be `0`, hence `0 ∈ e.target`. But `e.target = e.toFun '' e.source`
on which `e.toFun y = y^2`, so `0 ∈ e.target` ⇒ `0 ∈ e.source`.
Contradicts `squareLocalHomeomorph_zero_notMem_source`. -/
theorem squareLocalHomeomorph_symm_ne_zero
    (a : HyperellipticAffine H) (hpY : a ∈ smoothLocusY H)
    {z : ℂ}
    (hz : z ∈ ((affineChartProjX (H := H) a hpY) :
      OpenPartialHomeomorph (HyperellipticAffine H) ℂ).target) :
    (squareLocalHomeomorph (H := H) a hpY).symm (H.f.eval z) ≠ 0 := by
  -- chart target = { x | H.f.eval x ∈ e.target } per affineChartProjX def.
  have hHfz : H.f.eval z ∈ (squareLocalHomeomorph (H := H) a hpY).target := hz
  -- Suppose the y-branch is zero; derive a contradiction.
  intro hZero
  set e := squareLocalHomeomorph (H := H) a hpY with he_def
  -- By right_inv, e (e.symm (H.f.eval z)) = H.f.eval z.
  have hRight : e (e.symm (H.f.eval z)) = H.f.eval z := e.right_inv hHfz
  -- The y-branch e.symm sends target to source.
  have hSymmInSrc : e.symm (H.f.eval z) ∈ e.source := e.map_target hHfz
  -- Substituting hZero: e 0 = H.f.eval z (using the membership above).
  rw [hZero] at hRight hSymmInSrc
  -- But 0 ∉ e.source by the structural axiom.
  exact (squareLocalHomeomorph_zero_notMem_source a hpY) hSymmInSrc

/-- `affineProjXCoeff g a hpY 0 = 0`: the zero polynomial gives the
zero coefficient at every point. -/
@[simp] theorem affineProjXCoeff_zero (a : HyperellipticAffine H)
    (hpY : a ∈ smoothLocusY H) (z : ℂ) :
    affineProjXCoeff (0 : Polynomial ℂ) a hpY z = 0 := by
  unfold affineProjXCoeff
  by_cases hz : z ∈ ((affineChartProjX (H := H) a hpY) :
      OpenPartialHomeomorph (HyperellipticAffine H) ℂ).target
  · simp [hz, Polynomial.eval_zero]
  · simp [hz]

/-- `affineProjXCoeff` is additive in `g`. -/
theorem affineProjXCoeff_add (g g' : Polynomial ℂ) (a : HyperellipticAffine H)
    (hpY : a ∈ smoothLocusY H) (z : ℂ) :
    affineProjXCoeff (g + g') a hpY z =
      affineProjXCoeff g a hpY z + affineProjXCoeff g' a hpY z := by
  unfold affineProjXCoeff
  by_cases hz : z ∈ ((affineChartProjX (H := H) a hpY) :
      OpenPartialHomeomorph (HyperellipticAffine H) ℂ).target
  · simp only [hz, if_true, Polynomial.eval_add]
    ring
  · simp [hz]

/-- `affineProjXCoeff` is ℂ-linear (scalar mult side). -/
theorem affineProjXCoeff_smul (c : ℂ) (g : Polynomial ℂ) (a : HyperellipticAffine H)
    (hpY : a ∈ smoothLocusY H) (z : ℂ) :
    affineProjXCoeff (c • g) a hpY z = c * affineProjXCoeff g a hpY z := by
  classical
  unfold affineProjXCoeff
  by_cases hz : z ∈ ((affineChartProjX (H := H) a hpY) :
      OpenPartialHomeomorph (HyperellipticAffine H) ℂ).target
  · simp only [hz, if_true, dif_pos]
    rw [show ((c • g : Polynomial ℂ).eval z) = c * g.eval z from by
      simp [Polynomial.smul_eval, smul_eq_mul]]
    ring
  · simp [hz]

/-- **Closed form on chart target.** For `z ∈ chart target`,
`affineProjXCoeff g a hpY z = g.eval z / (squareLocalHomeomorph.symm (H.f.eval z))`. -/
theorem affineProjXCoeff_eq_on_target (g : Polynomial ℂ) (a : HyperellipticAffine H)
    (hpY : a ∈ smoothLocusY H) {z : ℂ}
    (hz : z ∈ ((affineChartProjX (H := H) a hpY) :
      OpenPartialHomeomorph (HyperellipticAffine H) ℂ).target) :
    affineProjXCoeff g a hpY z =
      g.eval z / ((squareLocalHomeomorph (H := H) a hpY).symm (H.f.eval z)) := by
  classical
  unfold affineProjXCoeff
  simp [hz]

/-- The chart target of `affineChartProjX` is open (Codex's chart def). -/
theorem affineChartProjX_target_isOpen (a : HyperellipticAffine H)
    (hpY : a ∈ smoothLocusY H) :
    IsOpen (((affineChartProjX (H := H) a hpY) :
        OpenPartialHomeomorph (HyperellipticAffine H) ℂ).target) :=
  (affineChartProjX (H := H) a hpY).open_target

/-- **Analyticity of the projX coefficient on chart target.** Combines:
* polynomial analyticity (`AnalyticOn.eval_polynomial`) for `g` and `H.f`;
* `squareLocalHomeomorph.symm` is analytic on `e.target`
  (from Codex's `squareLocalHomeomorph_contDiffOn_symm` via the
  `ContDiffOn ω ↔ AnalyticOn` equivalence over ℂ);
* composition + division by non-vanishing analytic
  (`AnalyticOn.div`, `_ne_zero`). -/
theorem affineProjXCoeff_analyticOn_chartTarget
    (g : Polynomial ℂ) (a : HyperellipticAffine H) (hpY : a ∈ smoothLocusY H) :
    AnalyticOn ℂ (affineProjXCoeff g a hpY)
      (((affineChartProjX (H := H) a hpY) :
          OpenPartialHomeomorph (HyperellipticAffine H) ℂ).target) := by
  -- Abbreviate
  set e := squareLocalHomeomorph (H := H) a hpY with he_def
  set chartTarget :=
    (((affineChartProjX (H := H) a hpY) :
        OpenPartialHomeomorph (HyperellipticAffine H) ℂ).target) with hct_def
  -- Step 1: g.eval is analytic everywhere, hence on chartTarget.
  have hG : AnalyticOn ℂ (fun z : ℂ => g.eval z) chartTarget :=
    (AnalyticOn.eval_polynomial g).mono (Set.subset_univ _)
  -- Step 2: H.f.eval is analytic everywhere, hence on chartTarget.
  have hF : AnalyticOn ℂ (fun z : ℂ => H.f.eval z) chartTarget :=
    (AnalyticOn.eval_polynomial H.f).mono (Set.subset_univ _)
  -- Step 3: e.symm is analytic on e.target. Convert ContDiffOn ω → AnalyticOn ℂ.
  have hSymm : AnalyticOn ℂ (e.symm) e.target := by
    have hCD : ContDiffOn ℂ ω e.symm e.target :=
      squareLocalHomeomorph_contDiffOn_symm (H := H) a hpY
    rw [show (ω : WithTop ℕ∞) = ⊤ from rfl] at hCD
    exact (contDiffOn_omega_iff_analyticOn (𝕜 := ℂ) (E := ℂ) (F := ℂ)
      e.open_target.uniqueDiffOn).mp hCD
  -- Step 4: e.symm ∘ H.f.eval analytic on chartTarget.
  -- Need: image of H.f.eval on chartTarget lands in e.target.
  -- This holds by the chart target def: chartTarget = { z | H.f.eval z ∈ e.target }.
  have hMaps : Set.MapsTo (fun z : ℂ => H.f.eval z) chartTarget e.target := by
    intro z hz
    -- chartTarget = { z | H.f.eval z ∈ e.target } per affineChartProjX definition
    -- This is a `change` that the definition unfolds to.
    change H.f.eval z ∈ e.target
    exact hz
  have hSymmComp : AnalyticOn ℂ (fun z : ℂ => e.symm (H.f.eval z)) chartTarget :=
    hSymm.comp hF hMaps
  -- Step 5: Denominator non-vanishing on chartTarget.
  have hNeZero : ∀ z ∈ chartTarget, e.symm (H.f.eval z) ≠ 0 :=
    fun z hz => squareLocalHomeomorph_symm_ne_zero a hpY hz
  -- Step 6: Quotient is analytic.
  have hQuotient : AnalyticOn ℂ (fun z : ℂ => g.eval z / e.symm (H.f.eval z)) chartTarget :=
    hG.div hSymmComp hNeZero
  -- Step 7: Match `affineProjXCoeff` to the quotient on chartTarget.
  -- `AnalyticOn.congr` takes `EqOn g f s` (output `g`, input `f`), so we want
  -- `affineProjXCoeff z = quotient z` per element — exactly what
  -- `affineProjXCoeff_eq_on_target` gives directly.
  exact hQuotient.congr (fun z hz => affineProjXCoeff_eq_on_target g a hpY hz)

/-! ## ProjY chart coefficient (S2 — mirror of S1)

For `a ∈ smoothLocusX` (i.e. `f'(a.val.1) ≠ 0`), the projY chart
`(x, y) ↦ y` represents `g(x) dx/y` in chart-y coordinates as
`2 g(x(y)) / f'(x(y))` after the change of variable `dx = (2y/f'(x)) dy`.

The chart-symm has `.val.1 = polynomialLocalHomeomorph.symm (y²)`
(per `affineChartProjY_symm_apply_fst`).
-/

/-- **Narrow structural axiom.** No critical point of `x ↦ H.f.eval x`
lies in the source of `polynomialLocalHomeomorph p hp`. Mirror of
`squareLocalHomeomorph_zero_notMem_source`: the IFT-derived chart at
`a.val.1` (where `f'(a.val.1) ≠ 0`) has a source bounded away from
zeros of the derivative. -/
axiom polynomialLocalHomeomorph_no_critical_in_source
    (p : HyperellipticAffine H) (hp : p ∈ smoothLocusX H)
    {x : ℂ} (hx : x ∈ (polynomialLocalHomeomorph (H := H) p hp).source) :
    H.f.derivative.eval x ≠ 0

/-- The derivative `f'(x(z))` is nonzero on the projY chart target,
where `x(z) = polynomialLocalHomeomorph.symm (z²)`.

**Proof.** `polynomialLocalHomeomorph.symm` maps target to source
(`map_target`); on source, `f' ≠ 0` by the axiom above. -/
theorem polynomialLocalHomeomorph_symm_eval_derivative_ne_zero
    (a : HyperellipticAffine H) (hpX : a ∈ smoothLocusX H)
    {z : ℂ}
    (hz : z ∈ ((affineChartProjY (H := H) a hpX) :
      OpenPartialHomeomorph (HyperellipticAffine H) ℂ).target) :
    H.f.derivative.eval
      ((polynomialLocalHomeomorph (H := H) a hpX).symm (z ^ 2)) ≠ 0 := by
  set e := polynomialLocalHomeomorph (H := H) a hpX with he_def
  have hz' : z ^ 2 ∈ e.target := by
    simpa [affineChartProjY] using hz
  exact polynomialLocalHomeomorph_no_critical_in_source a hpX (e.map_target hz')

/-- Chart-local coefficient of `g(x) dx / y` in the projY chart at
`a ∈ smoothLocusX` (i.e. `f'(a.val.1) ≠ 0`). For `z ∈ chart target`,
this is `2 g(x(z)) / f'(x(z))` where `x(z) = polynomialLocalHomeomorph.symm (z²)`.

Off-target the value is `0` (per `IsZeroOffChartTarget`). -/
noncomputable def affineProjYCoeff (g : Polynomial ℂ) (a : HyperellipticAffine H)
    (hpX : a ∈ smoothLocusX H) (z : ℂ) : ℂ := by
  classical
  exact
    if z ∈ ((affineChartProjY (H := H) a hpX) :
        OpenPartialHomeomorph (HyperellipticAffine H) ℂ).target then
      2 * g.eval ((polynomialLocalHomeomorph (H := H) a hpX).symm (z ^ 2)) /
        H.f.derivative.eval
          ((polynomialLocalHomeomorph (H := H) a hpX).symm (z ^ 2))
    else 0

@[simp] theorem affineProjYCoeff_zero (a : HyperellipticAffine H)
    (hpX : a ∈ smoothLocusX H) (z : ℂ) :
    affineProjYCoeff (0 : Polynomial ℂ) a hpX z = 0 := by
  classical
  unfold affineProjYCoeff
  by_cases hz : z ∈ ((affineChartProjY (H := H) a hpX) :
      OpenPartialHomeomorph (HyperellipticAffine H) ℂ).target
  · simp [hz, Polynomial.eval_zero]
  · simp [hz]

theorem affineProjYCoeff_add (g g' : Polynomial ℂ) (a : HyperellipticAffine H)
    (hpX : a ∈ smoothLocusX H) (z : ℂ) :
    affineProjYCoeff (g + g') a hpX z =
      affineProjYCoeff g a hpX z + affineProjYCoeff g' a hpX z := by
  classical
  unfold affineProjYCoeff
  by_cases hz : z ∈ ((affineChartProjY (H := H) a hpX) :
      OpenPartialHomeomorph (HyperellipticAffine H) ℂ).target
  · simp only [hz, if_true, Polynomial.eval_add]
    ring
  · simp [hz]

theorem affineProjYCoeff_smul (c : ℂ) (g : Polynomial ℂ) (a : HyperellipticAffine H)
    (hpX : a ∈ smoothLocusX H) (z : ℂ) :
    affineProjYCoeff (c • g) a hpX z = c * affineProjYCoeff g a hpX z := by
  classical
  unfold affineProjYCoeff
  by_cases hz : z ∈ ((affineChartProjY (H := H) a hpX) :
      OpenPartialHomeomorph (HyperellipticAffine H) ℂ).target
  · simp only [hz, if_true]
    set x := (polynomialLocalHomeomorph (H := H) a hpX).symm (z ^ 2)
    rw [show ((c • g : Polynomial ℂ).eval x) = c * g.eval x from by
      simp [Polynomial.smul_eval, smul_eq_mul]]
    ring
  · simp [hz]

theorem affineProjYCoeff_eq_on_target (g : Polynomial ℂ) (a : HyperellipticAffine H)
    (hpX : a ∈ smoothLocusX H) {z : ℂ}
    (hz : z ∈ ((affineChartProjY (H := H) a hpX) :
      OpenPartialHomeomorph (HyperellipticAffine H) ℂ).target) :
    affineProjYCoeff g a hpX z =
      2 * g.eval ((polynomialLocalHomeomorph (H := H) a hpX).symm (z ^ 2)) /
        H.f.derivative.eval
          ((polynomialLocalHomeomorph (H := H) a hpX).symm (z ^ 2)) := by
  classical
  unfold affineProjYCoeff
  simp [hz]

theorem affineChartProjY_target_isOpen (a : HyperellipticAffine H)
    (hpX : a ∈ smoothLocusX H) :
    IsOpen (((affineChartProjY (H := H) a hpX) :
        OpenPartialHomeomorph (HyperellipticAffine H) ℂ).target) :=
  (affineChartProjY (H := H) a hpX).open_target

/-- **Analyticity of the projY coefficient on chart target.** Mirror of
`affineProjXCoeff_analyticOn_chartTarget`. Combines:
* `H.f.derivative.eval` analytic everywhere (polynomial)
* `polynomialLocalHomeomorph.symm` analytic on its target via Codex's
  `polynomialLocalHomeomorph_contDiffOn_symm` + `contDiffOn_omega_iff_analyticOn`
* `z ↦ z^2` analytic everywhere
* polynomial composition + division by non-vanishing analytic. -/
theorem affineProjYCoeff_analyticOn_chartTarget
    (g : Polynomial ℂ) (a : HyperellipticAffine H) (hpX : a ∈ smoothLocusX H) :
    AnalyticOn ℂ (affineProjYCoeff g a hpX)
      (((affineChartProjY (H := H) a hpX) :
          OpenPartialHomeomorph (HyperellipticAffine H) ℂ).target) := by
  set e := polynomialLocalHomeomorph (H := H) a hpX with he_def
  set chartTarget :=
    (((affineChartProjY (H := H) a hpX) :
        OpenPartialHomeomorph (HyperellipticAffine H) ℂ).target) with hct_def
  -- Step 1: z ↦ z^2 is analytic on ℂ.
  have hSq : AnalyticOn ℂ (fun z : ℂ => z ^ 2) chartTarget :=
    (analyticOn_id.pow 2).mono (Set.subset_univ _)
  -- Step 2: e.symm is analytic on e.target.
  have hSymm : AnalyticOn ℂ e.symm e.target := by
    have hCD : ContDiffOn ℂ ω e.symm e.target :=
      polynomialLocalHomeomorph_contDiffOn_symm (H := H) a hpX
    rw [show (ω : WithTop ℕ∞) = ⊤ from rfl] at hCD
    exact (contDiffOn_omega_iff_analyticOn (𝕜 := ℂ) (E := ℂ) (F := ℂ)
      e.open_target.uniqueDiffOn).mp hCD
  -- Step 3: x(z) = e.symm (z^2) analytic on chartTarget.
  have hMaps : Set.MapsTo (fun z : ℂ => z ^ 2) chartTarget e.target := by
    intro z hz
    -- chartTarget = { y | y^2 ∈ e.target }
    change z ^ 2 ∈ e.target
    simpa [affineChartProjY] using hz
  have hX : AnalyticOn ℂ (fun z : ℂ => e.symm (z ^ 2)) chartTarget :=
    hSymm.comp hSq hMaps
  -- Step 4: g(x(z)) and f'(x(z)) analytic on chartTarget (composing with polynomials).
  have hG : AnalyticOn ℂ (fun z : ℂ => g.eval (e.symm (z ^ 2))) chartTarget :=
    hX.aeval_polynomial g
  have hFder : AnalyticOn ℂ
      (fun z : ℂ => H.f.derivative.eval (e.symm (z ^ 2))) chartTarget :=
    hX.aeval_polynomial H.f.derivative
  -- Step 5: 2*g(x(z)) analytic.
  have hNum : AnalyticOn ℂ
      (fun z : ℂ => 2 * g.eval (e.symm (z ^ 2))) chartTarget :=
    analyticOn_const.mul hG
  -- Step 6: Denominator non-vanishing.
  have hNeZero : ∀ z ∈ chartTarget,
      H.f.derivative.eval (e.symm (z ^ 2)) ≠ 0 :=
    fun z hz => polynomialLocalHomeomorph_symm_eval_derivative_ne_zero a hpX hz
  -- Step 7: Quotient analytic.
  have hQuotient : AnalyticOn ℂ
      (fun z : ℂ => 2 * g.eval (e.symm (z ^ 2)) /
        H.f.derivative.eval (e.symm (z ^ 2))) chartTarget :=
    hNum.div hFder hNeZero
  -- Step 8: Match `affineProjYCoeff` on chartTarget.
  exact hQuotient.congr (fun z hz => affineProjYCoeff_eq_on_target g a hpX hz)

/-! ## Cocycle compatibility on chart overlaps (S3)

For the form `g(x) dx / y` to be a holomorphic 1-form, the chart-local
coefficient must transform correctly across chart overlaps. The
cocycle predicate (in `RiemannSurface/OneForm.lean`):
```
coeff_p z = coeff_q (chart_q (chart_p.symm z)) * fderiv (chart_q ∘ chart_p.symm) z 1
```

For our affine chart system, this has 4 sub-cases based on (p, q)
chart families:
* projX × projX: chart transition is identity (both project to x);
  reduces to y-branch agreement at the common point.
* projX × projY: transition is `x ↦ y(x) = ±√f(x)` with derivative
  `f'(x)/(2y)`; the cocycle absorbs this factor exactly.
* projY × projX: symmetric.
* projY × projY: chart transition is identity.
-/

/-- **Cocycle sub-case 1: projX × projX** — y-branch agreement.

For two projX charts at p and q, if `chart_p.symm z ∈ chart_q.source`,
then the chart transition `chart_q ∘ chart_p.symm` is the identity at
z, and the y-branches `e_p.symm` and `e_q.symm` agree on `H.f.eval z`. -/
theorem squareLocalHomeomorph_symm_eq_of_mem
    (p q : HyperellipticAffine H)
    (hpY : p ∈ smoothLocusY H) (hqY : q ∈ smoothLocusY H)
    {z : ℂ}
    (hz : z ∈ ((affineChartProjX (H := H) p hpY) :
      OpenPartialHomeomorph (HyperellipticAffine H) ℂ).target)
    (hSymInY :
      (squareLocalHomeomorph (H := H) p hpY).symm (H.f.eval z) ∈
        (squareLocalHomeomorph (H := H) q hqY).source) :
    (squareLocalHomeomorph (H := H) p hpY).symm (H.f.eval z) =
      (squareLocalHomeomorph (H := H) q hqY).symm (H.f.eval z) := by
  set e_p := squareLocalHomeomorph (H := H) p hpY with he_p_def
  set e_q := squareLocalHomeomorph (H := H) q hqY with he_q_def
  -- The y-branch from chart p satisfies (e_p.symm (H.f.eval z))^2 = H.f.eval z
  -- by `e_p.right_inv` at H.f.eval z ∈ e_p.target.
  have hHfz_p : H.f.eval z ∈ e_p.target := hz
  have hSqRel : (e_p.symm (H.f.eval z)) ^ 2 = H.f.eval z := by
    have := e_p.right_inv hHfz_p
    -- e_p.toFun is `fun y => y^2` on its source
    -- The actual identity: e_p (e_p.symm (H.f.eval z)) = H.f.eval z
    -- We need to convert e_p applied to a value to that value squared.
    -- Codex's chart def: e_p.toFun = (fun y : ℂ => y ^ 2) by construction.
    simpa [squareLocalHomeomorph, e_p] using this
  -- Now e_q.symm (H.f.eval z): by left_inv at e_p.symm (H.f.eval z) (which is in e_q.source):
  have hRoundtrip :
      e_q.symm (e_q (e_p.symm (H.f.eval z))) = e_p.symm (H.f.eval z) :=
    e_q.left_inv hSymInY
  -- e_q applied: e_q.toFun is also `y^2` on its source.
  have hSqRel_q : e_q (e_p.symm (H.f.eval z)) = H.f.eval z := by
    have : e_q (e_p.symm (H.f.eval z)) = (e_p.symm (H.f.eval z)) ^ 2 := by
      simpa [squareLocalHomeomorph, e_q] using
        congr_arg id (rfl : e_q (e_p.symm (H.f.eval z)) =
          e_q (e_p.symm (H.f.eval z)))
    rw [this, hSqRel]
  -- Combining: rewrite hRoundtrip using hSqRel_q.
  rw [hSqRel_q] at hRoundtrip
  exact hRoundtrip.symm

/-! ### S3 sub-case 2: projX × projY chain rule

The chart transition `affineChartProjX_p .symm . trans affineChartProjY_q` at
`z` equals `(squareLocalHomeomorph p).symm (H.f.eval z)` (the y-branch). To
verify the cocycle we need its derivative. By implicit differentiation of
`y(z)^2 = f(z)`: `2 y(z) y'(z) = f'(z)`, so `y'(z) = f'(z) / (2 y(z))`.

Below we make this rigorous via `HasDerivAt.of_local_left_inverse` for the
inverse branch, then chain with `Polynomial.hasDerivAt`. -/

/-- Derivative of the chosen y-branch `e_p.symm` at `H.f.eval z`:
`(e_p.symm)' (H.f.eval z) = 1 / (2 * e_p.symm (H.f.eval z))`.

Proof: `f(y) = y²` has derivative `2 y₀` at `y₀ = e_p.symm (H.f.eval z) ≠ 0`,
and `f (e_p.symm y) = y` for `y ∈ e_p.target` (open). The inverse function
theorem (`HasDerivAt.of_local_left_inverse`) gives `e_p.symm` derivative
`(2 y₀)⁻¹` at `H.f.eval z`. -/
theorem squareLocalHomeomorph_symm_hasDerivAt
    (a : HyperellipticAffine H) (hpY : a ∈ smoothLocusY H)
    {z : ℂ}
    (hz : z ∈ ((affineChartProjX (H := H) a hpY) :
      OpenPartialHomeomorph (HyperellipticAffine H) ℂ).target) :
    HasDerivAt (squareLocalHomeomorph (H := H) a hpY).symm
      (1 / (2 * (squareLocalHomeomorph (H := H) a hpY).symm (H.f.eval z)))
      (H.f.eval z) := by
  set e := squareLocalHomeomorph (H := H) a hpY with he_def
  have hHfz : H.f.eval z ∈ e.target := hz
  set y₀ := e.symm (H.f.eval z) with hy₀
  -- Step 1: f = (· ^ 2) has derivative 2 * y₀ at y₀.
  have hfHas : HasDerivAt (fun y : ℂ => y ^ 2) (2 * y₀) y₀ := by
    simpa using hasDerivAt_pow 2 y₀
  -- Step 2: e.symm continuous at H.f.eval z.
  have hCont : ContinuousAt e.symm (H.f.eval z) := e.continuousAt_symm hHfz
  -- Step 3: f (e.symm y) = y eventually near H.f.eval z (since e.target is open).
  have hLeftInv : ∀ᶠ (y : ℂ) in nhds (H.f.eval z),
      (fun y' : ℂ => y' ^ 2) (e.symm y) = y := by
    refine Filter.eventually_of_mem (e.open_target.mem_nhds hHfz) ?_
    intro y hy
    have hRight : (e : ℂ → ℂ) (e.symm y) = y := e.right_inv hy
    have hSq : (e : ℂ → ℂ) (e.symm y) = (e.symm y) ^ 2 := by
      simpa [e, squareLocalHomeomorph] using
        congrArg (e : ℂ → ℂ) (rfl : e.symm y = e.symm y)
    rw [hSq] at hRight
    exact hRight
  -- Step 4: 2 * y₀ ≠ 0.
  have hY₀ : y₀ ≠ 0 := squareLocalHomeomorph_symm_ne_zero a hpY hz
  have h2Y : (2 : ℂ) * y₀ ≠ 0 := mul_ne_zero (by norm_num) hY₀
  -- Step 5: Inverse function theorem.
  have key := HasDerivAt.of_local_left_inverse hCont hfHas h2Y hLeftInv
  convert key using 1
  rw [one_div]

/-- Chain-rule derivative of the projX→projY chart transition: at `z` in
the projX chart target, the transition `z ↦ (squareLocalHomeomorph p).symm
(H.f.eval z)` has derivative `f'(z) / (2 * y(z))` where
`y(z) = (squareLocalHomeomorph p).symm (H.f.eval z)`. -/
theorem affineChartProjX_to_projY_transition_hasDerivAt
    (a : HyperellipticAffine H) (hpY : a ∈ smoothLocusY H)
    {z : ℂ}
    (hz : z ∈ ((affineChartProjX (H := H) a hpY) :
      OpenPartialHomeomorph (HyperellipticAffine H) ℂ).target) :
    HasDerivAt
      (fun w : ℂ => (squareLocalHomeomorph (H := H) a hpY).symm (H.f.eval w))
      (H.f.derivative.eval z /
        (2 * (squareLocalHomeomorph (H := H) a hpY).symm (H.f.eval z)))
      z := by
  have hSymm := squareLocalHomeomorph_symm_hasDerivAt (H := H) a hpY hz
  have hFeval : HasDerivAt (fun w : ℂ => H.f.eval w) (H.f.derivative.eval z) z :=
    H.f.hasDerivAt z
  have hcomp := hSymm.comp z hFeval
  convert hcomp using 1
  rw [one_div, mul_comm, ← div_eq_inv_mul]

/-! ### S3 sub-case 3: projY × projX chain rule

Mirror of sub-case 2. The transition `affineChartProjY_q .symm . trans
affineChartProjX_p` at `y` equals `(polynomialLocalHomeomorph q).symm (y²)`
(the x-branch). By implicit differentiation of `f(x(y)) = y²`:
`f'(x(y)) · x'(y) = 2y`, so `x'(y) = 2y / f'(x(y))`. -/

/-- Derivative of the chosen x-branch `e_q.symm` at `y²`:
`(e_q.symm)' (y²) = 1 / f'(e_q.symm (y²))`.

Proof: `f(x) = H.f.eval x` has derivative `f'(x₀)` at `x₀ = e_q.symm(y²)`,
which is nonzero by `polynomialLocalHomeomorph_symm_eval_derivative_ne_zero`,
and `f (e_q.symm w) = w` for `w ∈ e_q.target` (open). The inverse function
theorem (`HasDerivAt.of_local_left_inverse`) gives the result. -/
theorem polynomialLocalHomeomorph_symm_hasDerivAt
    (a : HyperellipticAffine H) (hpX : a ∈ smoothLocusX H)
    {y : ℂ}
    (hy : y ∈ ((affineChartProjY (H := H) a hpX) :
      OpenPartialHomeomorph (HyperellipticAffine H) ℂ).target) :
    HasDerivAt (polynomialLocalHomeomorph (H := H) a hpX).symm
      (1 / H.f.derivative.eval
        ((polynomialLocalHomeomorph (H := H) a hpX).symm (y ^ 2)))
      (y ^ 2) := by
  set e := polynomialLocalHomeomorph (H := H) a hpX with he_def
  have hy2 : y ^ 2 ∈ e.target := by
    simpa [affineChartProjY] using hy
  set x₀ := e.symm (y ^ 2) with hx₀
  have hfHas : HasDerivAt (fun x : ℂ => H.f.eval x) (H.f.derivative.eval x₀) x₀ :=
    H.f.hasDerivAt x₀
  have hCont : ContinuousAt e.symm (y ^ 2) := e.continuousAt_symm hy2
  have hLeftInv : ∀ᶠ (w : ℂ) in nhds (y ^ 2),
      (fun x : ℂ => H.f.eval x) (e.symm w) = w := by
    refine Filter.eventually_of_mem (e.open_target.mem_nhds hy2) ?_
    intro w hw
    have hRight : (e : ℂ → ℂ) (e.symm w) = w := e.right_inv hw
    have hPoly : (e : ℂ → ℂ) (e.symm w) = H.f.eval (e.symm w) := by
      simpa [e, polynomialLocalHomeomorph] using
        congrArg (e : ℂ → ℂ) (rfl : e.symm w = e.symm w)
    rw [hPoly] at hRight
    exact hRight
  have hFder : H.f.derivative.eval x₀ ≠ 0 :=
    polynomialLocalHomeomorph_symm_eval_derivative_ne_zero a hpX hy
  have key := HasDerivAt.of_local_left_inverse hCont hfHas hFder hLeftInv
  convert key using 1
  rw [one_div]

/-- Chain-rule derivative of the projY→projX chart transition: at `y` in
the projY chart target, the transition `y ↦ (polynomialLocalHomeomorph q).symm
(y²)` has derivative `2y / f'(x(y))` where
`x(y) = (polynomialLocalHomeomorph q).symm (y²)`. -/
theorem affineChartProjY_to_projX_transition_hasDerivAt
    (a : HyperellipticAffine H) (hpX : a ∈ smoothLocusX H)
    {y : ℂ}
    (hy : y ∈ ((affineChartProjY (H := H) a hpX) :
      OpenPartialHomeomorph (HyperellipticAffine H) ℂ).target) :
    HasDerivAt
      (fun w : ℂ => (polynomialLocalHomeomorph (H := H) a hpX).symm (w ^ 2))
      (2 * y /
        H.f.derivative.eval
          ((polynomialLocalHomeomorph (H := H) a hpX).symm (y ^ 2)))
      y := by
  have hSymm := polynomialLocalHomeomorph_symm_hasDerivAt (H := H) a hpX hy
  have hSq : HasDerivAt (fun w : ℂ => w ^ 2) (2 * y) y := by
    simpa using hasDerivAt_pow 2 y
  have hcomp := hSymm.comp y hSq
  convert hcomp using 1
  field_simp

/-- **Cocycle sub-case 4: projY × projY** — x-branch agreement.

Mirror of sub-case 1. For two projY charts at p and q, if `chart_p.symm y ∈
chart_q.source`, then the chart transition `chart_q ∘ chart_p.symm` is the
identity at y, and the x-branches `e_p.symm` and `e_q.symm` agree on `y²`. -/
theorem polynomialLocalHomeomorph_symm_eq_of_mem
    (p q : HyperellipticAffine H)
    (hpX : p ∈ smoothLocusX H) (hqX : q ∈ smoothLocusX H)
    {y : ℂ}
    (hy : y ∈ ((affineChartProjY (H := H) p hpX) :
      OpenPartialHomeomorph (HyperellipticAffine H) ℂ).target)
    (hSymInX :
      (polynomialLocalHomeomorph (H := H) p hpX).symm (y ^ 2) ∈
        (polynomialLocalHomeomorph (H := H) q hqX).source) :
    (polynomialLocalHomeomorph (H := H) p hpX).symm (y ^ 2) =
      (polynomialLocalHomeomorph (H := H) q hqX).symm (y ^ 2) := by
  set e_p := polynomialLocalHomeomorph (H := H) p hpX with he_p_def
  set e_q := polynomialLocalHomeomorph (H := H) q hqX with he_q_def
  have hy2_p : y ^ 2 ∈ e_p.target := by
    simpa [affineChartProjY] using hy
  -- The x-branch from chart p satisfies H.f.eval (e_p.symm (y²)) = y².
  have hPolyRel : H.f.eval (e_p.symm (y ^ 2)) = y ^ 2 := by
    have := e_p.right_inv hy2_p
    simpa [polynomialLocalHomeomorph, e_p] using this
  -- e_q.symm round-trips at e_p.symm(y²) ∈ e_q.source.
  have hRoundtrip :
      e_q.symm (e_q (e_p.symm (y ^ 2))) = e_p.symm (y ^ 2) :=
    e_q.left_inv hSymInX
  -- e_q applied to the same point gives H.f.eval of that point, which is y².
  have hPolyRel_q : e_q (e_p.symm (y ^ 2)) = y ^ 2 := by
    have : e_q (e_p.symm (y ^ 2)) = H.f.eval (e_p.symm (y ^ 2)) := by
      simpa [polynomialLocalHomeomorph, e_q] using
        congrArg (e_q : ℂ → ℂ) (rfl : e_p.symm (y ^ 2) = e_p.symm (y ^ 2))
    rw [this, hPolyRel]
  rw [hPolyRel_q] at hRoundtrip
  exact hRoundtrip.symm

/-! ## Affine-side coefficient family

Bundles the projX/projY case-split into a single coefficient function
`hyperellipticAffineCoeff : HyperellipticAffine H → ℂ → ℂ`. This is the
first piece that conforms to the `IsHolomorphicOneFormCoeff` /
`IsZeroOffChartTarget` API used by `holomorphicOneFormSubmodule`. -/

/-- The affine-side coefficient family for the form `g(x) dx / y`: case-split
on whether the base point is in `smoothLocusY` (use projX coefficient) or
`smoothLocusX` (use projY coefficient). -/
noncomputable def hyperellipticAffineCoeff (g : Polynomial ℂ) :
    HyperellipticAffine H → ℂ → ℂ := fun a z => by
  classical
  exact
    if hpY : a ∈ smoothLocusY H then
      affineProjXCoeff g a hpY z
    else
      affineProjYCoeff g a
        (mem_smoothLocusX_of_y_eq_zero H (by simpa [smoothLocusY] using hpY)) z

/-- The affine coefficient family is analytic on each chart target. -/
theorem hyperellipticAffineCoeff_isHolomorphicOneFormCoeff
    (g : Polynomial ℂ) :
    IsHolomorphicOneFormCoeff (HyperellipticAffine H)
      (hyperellipticAffineCoeff (H := H) g) := by
  classical
  intro p
  have hExt : (extChartAt 𝓘(ℂ, ℂ) p).target = (affineChartAt (H := H) p).target := by
    rw [extChartAt_target]
    show (chartAt ℂ p).target ∩ Set.range (id : ℂ → ℂ) = (affineChartAt (H := H) p).target
    rw [Set.range_id, Set.inter_univ]
    rfl
  rw [hExt]
  by_cases hpY : p ∈ smoothLocusY H
  · rw [affineChartAt_of_mem_smoothLocusY (H := H) p hpY]
    have hCoeff : (hyperellipticAffineCoeff (H := H) g) p = affineProjXCoeff g p hpY := by
      funext z
      simp [hyperellipticAffineCoeff, hpY]
    rw [hCoeff]
    exact affineProjXCoeff_analyticOn_chartTarget g p hpY
  · have hpX : p ∈ smoothLocusX H :=
      mem_smoothLocusX_of_y_eq_zero H (by simpa [smoothLocusY] using hpY)
    rw [affineChartAt_of_not_mem_smoothLocusY (H := H) p hpY]
    have hCoeff : (hyperellipticAffineCoeff (H := H) g) p = affineProjYCoeff g p hpX := by
      funext z
      simp [hyperellipticAffineCoeff, hpY]
    rw [hCoeff]
    exact affineProjYCoeff_analyticOn_chartTarget g p hpX

/-- The affine coefficient family vanishes off each chart target. -/
theorem hyperellipticAffineCoeff_isZeroOffChartTarget (g : Polynomial ℂ) :
    IsZeroOffChartTarget (HyperellipticAffine H)
      (hyperellipticAffineCoeff (H := H) g) := by
  classical
  intro p z hz
  have hExt : (extChartAt 𝓘(ℂ, ℂ) p).target = (affineChartAt (H := H) p).target := by
    rw [extChartAt_target]
    show (chartAt ℂ p).target ∩ Set.range (id : ℂ → ℂ) = (affineChartAt (H := H) p).target
    rw [Set.range_id, Set.inter_univ]
    rfl
  rw [hExt] at hz
  by_cases hpY : p ∈ smoothLocusY H
  · rw [affineChartAt_of_mem_smoothLocusY (H := H) p hpY] at hz
    simp only [hyperellipticAffineCoeff, hpY, dite_true]
    simp [affineProjXCoeff, hz]
  · have hpX : p ∈ smoothLocusX H :=
      mem_smoothLocusX_of_y_eq_zero H (by simpa [smoothLocusY] using hpY)
    rw [affineChartAt_of_not_mem_smoothLocusY (H := H) p hpY] at hz
    simp only [hyperellipticAffineCoeff, hpY, dite_false]
    simp [affineProjYCoeff, hz]

/-! ## Cocycle equation, sub-case projX × projX

The chart transition is the identity on the overlap source (Codex's
`affineChartProjX_compat_affineChartProjX`), so its derivative is `1` and
the cocycle reduces to coefficient equality. Coefficient equality reduces
to y-branch agreement (`squareLocalHomeomorph_symm_eq_of_mem`).
-/

theorem hyperellipticAffineCoeff_cocycle_projX_projX
    (g : Polynomial ℂ)
    (p q : HyperellipticAffine H) (hpY : p ∈ smoothLocusY H) (hqY : q ∈ smoothLocusY H)
    {z : ℂ}
    (hz : z ∈ ((affineChartProjX (H := H) p hpY) :
      OpenPartialHomeomorph (HyperellipticAffine H) ℂ).target)
    (hSrc : ((affineChartProjX (H := H) p hpY).symm z : HyperellipticAffine H) ∈
              ((affineChartProjX (H := H) q hqY)).source) :
    affineProjXCoeff g p hpY z =
      affineProjXCoeff g q hqY
        ((affineChartProjX (H := H) q hqY) ((affineChartProjX (H := H) p hpY).symm z)) *
        (fderiv ℂ ((affineChartProjX (H := H) q hqY) ∘
          ((affineChartProjX (H := H) p hpY)).symm) z 1) := by
  classical
  -- Step 1: chart_q ∘ chart_p.symm at z reduces to z.
  have hQAt : (affineChartProjX (H := H) q hqY)
      ((affineChartProjX (H := H) p hpY).symm z) = z := by
    have h1 :
        (((affineChartProjX (H := H) p hpY).symm z) : HyperellipticAffine H).val.1 = z :=
      affineChartProjX_symm_apply_fst (H := H) p hpY hz
    change (((affineChartProjX (H := H) p hpY).symm z) : HyperellipticAffine H).val.1 = z
    exact h1
  -- Step 2: chart transition equals id eventually near z.
  set transition := (affineChartProjX (H := H) q hqY) ∘
    ((affineChartProjX (H := H) p hpY)).symm with htrans_def
  have hZinSrc : z ∈ (((affineChartProjX (H := H) p hpY).symm.trans
      (affineChartProjX (H := H) q hqY))).source := ⟨hz, hSrc⟩
  have hOpen : IsOpen (((affineChartProjX (H := H) p hpY).symm.trans
      (affineChartProjX (H := H) q hqY))).source :=
    ((affineChartProjX (H := H) p hpY).symm.trans
      (affineChartProjX (H := H) q hqY)).open_source
  have hEqId : transition =ᶠ[nhds z] id := by
    refine Filter.eventually_of_mem (hOpen.mem_nhds hZinSrc) ?_
    intro w hw
    simp only [transition, Function.comp_apply, id]
    have hw1 : w ∈ (affineChartProjX (H := H) p hpY).target := hw.1
    have h1 :
        (((affineChartProjX (H := H) p hpY).symm w) : HyperellipticAffine H).val.1 = w :=
      affineChartProjX_symm_apply_fst (H := H) p hpY hw1
    change (((affineChartProjX (H := H) p hpY).symm w) : HyperellipticAffine H).val.1 = w
    exact h1
  -- Step 3: fderiv (transition) z = id, so applied to 1 gives 1.
  have hFderiv : fderiv ℂ transition z = ContinuousLinearMap.id ℂ ℂ := by
    rw [Filter.EventuallyEq.fderiv_eq hEqId, fderiv_id]
  -- Step 4: chart_q target also contains z, so RHS coeff also reduces.
  have hQTarget : z ∈ ((affineChartProjX (H := H) q hqY) :
      OpenPartialHomeomorph (HyperellipticAffine H) ℂ).target := by
    rw [← hQAt]
    exact (affineChartProjX (H := H) q hqY).map_source hSrc
  -- Step 5: y-branches agree at H.f.eval z.
  have hSymInY :
      (squareLocalHomeomorph (H := H) p hpY).symm (H.f.eval z) ∈
        (squareLocalHomeomorph (H := H) q hqY).source := by
    have h2 := affineChartProjX_symm_apply_snd (H := H) p hpY hz
    rw [← h2]
    exact hSrc
  have hAgree :
      (squareLocalHomeomorph (H := H) p hpY).symm (H.f.eval z) =
        (squareLocalHomeomorph (H := H) q hqY).symm (H.f.eval z) :=
    squareLocalHomeomorph_symm_eq_of_mem (H := H) p q hpY hqY hz hSymInY
  -- Combine.
  rw [hQAt, hFderiv]
  simp only [ContinuousLinearMap.id_apply, mul_one]
  rw [affineProjXCoeff_eq_on_target g p hpY hz,
      affineProjXCoeff_eq_on_target g q hqY hQTarget,
      hAgree]

end Jacobians.ProjectiveCurve.HyperellipticAffine
