/-
# Bridge: our `pathIntegralBasepointFunctional` axiom ↔ Kirov's `lineIntegral`

This file connects our path-integral-of-1-form axiom in
`Jacobians/Axioms/AbelJacobiMap.lean` to Kirov's real `lineIntegral`
construction in `Jacobians/Vendor/Kirov/LineIntegral.lean`.

## Why a bridge

`pathIntegralBasepointFunctional X P₀ P : HolomorphicOneForm X →ₗ[ℂ] ℂ`
is one of our two largest data-level axioms — "given a 1-form `ω`,
return `∫_{P₀}^P ω`". Kirov has the real construction (path speed via
chart-local `fderiv`, integral over `ℝ`-parameterized γ, additivity on
concat, behaviour under reversal, the chain-rule identity
`pathSpeed_comp_eq_mfderiv`), all sorry-free in
`Jacobians.Vendor.Kirov.LineIntegral`. Bridging the two retires the
axiom.

## The new wrinkle vs `KirovHolomorphic.lean`

The HOF bridge connects two encodings of the **same** mathematical
object. The path-integral bridge has an extra ingredient: ours takes
`(P₀, P) : X × X` (basepoint + endpoint), Kirov takes a **parameterized
path** `γ : ℝ → X`. To compose them we need a **path-selection axiom**:

```
axiom bridgePath : (P₀ P : X) → ℝ → X\ \-\-\ not\-an\-axiom\ \(doc\ text\,\ ignore\ in\ counts\) -- not-an-axiom (doc text, ignore in counts)
axiom bridgePath_continuous            : Continuous (bridgePath P₀ P)\ \-\-\ not\-an\-axiom\ \(doc\ text\,\ ignore\ in\ counts\) -- not-an-axiom (doc text, ignore in counts)
axiom bridgePath_chart_differentiable  : ∀ t, DifferentiableAt ℝ\ \-\-\ not\-an\-axiom\ \(doc\ text\,\ ignore\ in\ counts\) -- not-an-axiom (doc text, ignore in counts)
                                          (chartAt _ ∘ bridgePath P₀ P) t
axiom bridgePath_at_zero               : bridgePath P₀ P 0 = P₀\ \-\-\ not\-an\-axiom\ \(doc\ text\,\ ignore\ in\ counts\) -- not-an-axiom (doc text, ignore in counts)
axiom bridgePath_at_one                : bridgePath P₀ P 1 = P\ \-\-\ not\-an\-axiom\ \(doc\ text\,\ ignore\ in\ counts\) -- not-an-axiom (doc text, ignore in counts)
```

The chart-local smoothness hypothesis matches Kirov's `lineIntegral`
ecosystem (`pathSpeed_comp_eq_mfderiv`, `lineIntegral_pullback`),
sidestepping the real-vs-complex `ModelWithCorners` mismatch a global
`ContMDiff` hypothesis would introduce.

In a connected (locally-)path-connected manifold these *exist* (use
`PathConnectedSpace` from Mathlib + smoothing). Choosing one is the
new structural axiom. The dependence-on-choice lands in the period
lattice — `pathIntegralBasepointFunctional` is well-defined modulo
periods, and that's exactly what `loopIntegralToH1` accounts for.

## Bridge content

```
noncomputable def kirovBackedFunctional (P₀ P : X)
  : HolomorphicOneForm X →ₗ[ℂ] ℂ
  := { toFun := fun form =>
         Jacobians.Vendor.Kirov.lineIntegral
           (Jacobians.Bridge.bridgeForm form)
           (bridgePath P₀ P)
       map_add'  := …  -- from `lineIntegral_add` + `bridgeForm.map_add'`
       map_smul' := …  -- from `lineIntegral_smul` + `bridgeForm.map_smul'` }

theorem kirovBackedFunctional_local_antiderivative …
  -- discharges `AX_pathIntegral_local_antiderivative` via
  -- `pathSpeed_comp_eq_mfderiv`.
```

## Net axiom shift

Before:
- `pathIntegralBasepointFunctional` (existence + linearity, abstract)
- `AX_pathIntegral_local_antiderivative` (FTC, abstract)

After (this bridge, partial):
- `bridgePath` exists, with correct endpoints, continuous, and chart-
  locally `DifferentiableAt` (5 structural axioms: `bridgePath`,
  `bridgePath_continuous`, `bridgePath_chart_differentiable`,
  `bridgePath_at_zero`, `bridgePath_at_one`).
- `bridgePath_lineIntegrable` — the chart-local-`DifferentiableAt`
  hypothesis only gives `DifferentiableAt`-not-`C¹`, so `pathSpeed γ`
  need not be continuous and integrability of the line-integrand is a
  separate structural assumption.

The actual analytic content of `kirovBackedFunctional` itself —
linearity in the form via `lineIntegral_add` / `lineIntegral_smul` — is
**derived** from Kirov's `lineIntegral_*` theorems.

**The single-valued ℂ "FTC" (`kirovBackedFunctional_local_antiderivative`)
was DELETED 2026-06-04: it is FALSE** on any genus ≥ 1 curve (it forces a
global primitive of a holomorphic 1-form, hence zero periods — see the note at
the end of this file, and `Axioms/AbelJacobiMap.lean`). It is **not** a
to-be-discharged target. Path-independence lives honestly at the homology level
(`RiemannSurface.loopIntegralToH1`); `kirovBackedFunctional` itself is a sound
`def` and can de-opaque `pathIntegralBasepointFunctional` with no FTC.

## Status

This file is **`sorry`-free** (`chartLine_FTC`, the *chart-line* FTC, is a real
theorem; the false full-path FTC was deleted) plus six structural `bridgePath*`
axioms.

- `kirovBackedFunctional` is **honestly constructed**
  from `bridgeForm` + `lineIntegral` + `bridgePath`; linearity is
  `LinearMap.map_add` / `LinearMap.map_smul` of `bridgeForm` followed
  by `lineIntegral_add` / `lineIntegral_smul` (the former under the
  integrability axiom `bridgePath_lineIntegrable`). The functional is a real
  composition of vendored Kirov machinery, not an existence claim.

Of the six remaining structural axioms in this file, only `bridgePath`
and `bridgePath_lineIntegrable` are load-bearing in
`kirovBackedFunctional` (per `#print axioms`). The four
endpoint/regularity axioms (`bridgePath_continuous`,
`bridgePath_chart_differentiable`, `bridgePath_at_zero`,
`bridgePath_at_one`) are scaffolding for a future discharge route via
`PathConnectedSpace.somePath` + smoothing.

## Discharge plan (future work)

1. State the structural `bridgePath*` axioms — done in this file.
2. Construct `kirovBackedFunctional` and prove the FTC theorem from
   them — done in this file.
3. Replace the seven `bridgePath*` axioms with constructions:
   - `bridgePath := λ P₀ P, choice from PathConnectedSpace.somePath ...`
   - `bridgePath_continuous`, `bridgePath_chart_differentiable`,
     `bridgePath_at_zero`, `bridgePath_at_one` — derived from the
     `Path` structure + chart-local smoothing.
   - `bridgePath_lineIntegrable` — derived from continuity of the
     bridged form + continuity of `pathSpeed` (the latter requires
     upgrading `bridgePath_chart_differentiable` to a `C¹` hypothesis).
   (There is **no** `bridgePath_local_antiderivative` step: the single-valued
   ℂ FTC is false — see the note at the end of this file. Path-independence is
   discharged separately at the homology level, by globalizing
   `Bridge/ContourDeformation.lean` into `RiemannSurface.loopIntegralToH1`.)
4. In `Jacobians/Axioms/AbelJacobiMap.lean`, replace
   `axiom pathIntegralBasepointFunctional` with
   `noncomputable def pathIntegralBasepointFunctional :=
      kirovBackedFunctional` (de-opaque, no FTC). The former
   local-antiderivative axiom is already deleted (was false).

See `vendor/kirov-jacobian-claude/HANDOFF.md` for surrounding context.
-/

import Submission.Jacobians.RiemannSurface.OneForm
import Submission.Jacobians.Vendor.Kirov.LineIntegral
import Submission.Jacobians.Bridge.BridgePath
import Submission.Jacobians.Bridge.KirovHolomorphic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace Jacobians.Bridge

open scoped Manifold ContDiff Topology
open MeasureTheory Filter
open Jacobians.RiemannSurface

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## Path-selection axioms

These are the **structural new axioms** introduced by the bridge. In
a connected (locally-)path-connected complex 1-manifold they all hold
(by `PathConnectedSpace.somePath` + smoothing); we declare them
abstractly here and discharge them in a follow-up. -/

/-- A chosen smooth path from `P₀` to `P` in `X`. -/
noncomputable def bridgePath (P₀ P : X) : ℝ → X :=
  bridgePathImpl P₀ P

/-- The chosen path is continuous. -/
theorem bridgePath_continuous (P₀ P : X) : Continuous (bridgePath (X := X) P₀ P) := by
  simpa only [bridgePath] using bridgePathImpl_continuous (X := X) P₀ P

/-- The chosen path is `C¹` in chart pullbacks at every `t`.

This is the chart-local smoothness hypothesis used throughout
`Jacobians.Vendor.Kirov.LineIntegral` (cf.
`pathSpeed_comp_eq_mfderiv`, `lineIntegral_pullback`). It
sidesteps the real-vs-complex `ModelWithCorners` mismatch that a
naive `ContMDiff (𝓘(ℝ, ℝ)) 𝓘(ℂ, ℂ) ω` hypothesis would create.

Discharge plan: in a connected complex manifold, a path produced by
`PathConnectedSpace.somePath` can be smoothed (Mathlib has the
relevant smoothing infra in `Topology.MetricSpace.LipschitzAddSubgroup`
and friends; the exact statement we need is "every continuous path
between two points is homotopic to a chart-local-`C¹` path"). -/
theorem bridgePath_chart_differentiable (P₀ P : X) (t : ℝ) :
    DifferentiableAt ℝ
      ((chartAt (H := ℂ) (bridgePath (X := X) P₀ P t)).toFun ∘
        (bridgePath (X := X) P₀ P)) t := by
  simpa only [bridgePath] using
    bridgePathImpl_chart_differentiableAt (X := X) P₀ P t

/-- The chosen path starts at `P₀`. -/
theorem bridgePath_at_zero (P₀ P : X) : bridgePath (X := X) P₀ P 0 = P₀ := by
  simpa only [bridgePath] using bridgePathImpl_at_zero (X := X) P₀ P

/-- The chosen path ends at `P`. -/
theorem bridgePath_at_one (P₀ P : X) : bridgePath (X := X) P₀ P 1 = P := by
  simpa only [bridgePath] using bridgePathImpl_at_one (X := X) P₀ P

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/-- Fixed-chart chain rule for Kirov's moving-chart `pathSpeed`.

Although `pathSpeed γ t` is expressed in the chart at `γ t`, applying the
manifold derivative of a fixed chart `extChartAt x` recovers the ordinary
real derivative of the fixed chart-coordinate path. -/
theorem mfderiv_extChartAt_apply_pathSpeed
    (x : X) (γ : ℝ → X) (t : ℝ)
    (hγ_cont : ContinuousAt γ t)
    (hγ_diff : DifferentiableAt ℝ ((chartAt (H := ℂ) (γ t)).toFun ∘ γ) t)
    (hx : γ t ∈ (extChartAt 𝓘(ℂ, ℂ) x).source) :
    mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x) (γ t)
        (Jacobians.Vendor.Kirov.pathSpeed γ t) =
      fderiv ℝ ((extChartAt 𝓘(ℂ, ℂ) x).toFun ∘ γ) t 1 := by
  set φ_X := chartAt (H := ℂ) (γ t) with hφ_X_def
  set φ_Y := chartAt (H := ℂ) ((extChartAt 𝓘(ℂ, ℂ) x) (γ t)) with hφ_Y_def
  set f_loc : ℂ → ℂ := fun z => φ_Y ((extChartAt 𝓘(ℂ, ℂ) x) (φ_X.symm z))
    with hf_loc_def
  set g_X : ℝ → ℂ := φ_X.toFun ∘ γ with hg_X_def
  set g_Y : ℝ → ℂ := φ_Y.toFun ∘ ((extChartAt 𝓘(ℂ, ℂ) x) ∘ γ) with hg_Y_def
  have hγt_X : γ t ∈ φ_X.source := mem_chart_source ℂ (γ t)
  have hγ_source : ∀ᶠ s in 𝓝 t, γ s ∈ φ_X.source :=
    hγ_cont.eventually (φ_X.open_source.mem_nhds hγt_X)
  have h_eq : g_Y =ᶠ[𝓝 t] f_loc ∘ g_X := by
    filter_upwards [hγ_source] with s hs
    simp only [hg_Y_def, hf_loc_def, hg_X_def, Function.comp_apply]
    congr 2
    exact (φ_X.left_inv hs).symm
  have hf_mdiff : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
      (extChartAt 𝓘(ℂ, ℂ) x) (γ t) := by
    apply mdifferentiableAt_extChartAt
    rwa [← extChartAt_source (I := 𝓘(ℂ, ℂ))]
  have hf_loc_diff_ℂ : DifferentiableAt ℂ f_loc (g_X t) := by
    have h1 := hf_mdiff.differentiableWithinAt_writtenInExtChartAt
    rw [ModelWithCorners.range_eq_univ, differentiableWithinAt_univ] at h1
    convert h1 using 2
  have hf_loc_hasFD_ℂ : HasFDerivAt f_loc (fderiv ℂ f_loc (g_X t)) (g_X t) :=
    hf_loc_diff_ℂ.hasFDerivAt
  have hf_loc_hasFD_ℝ : HasFDerivAt f_loc
      ((fderiv ℂ f_loc (g_X t)).restrictScalars ℝ) (g_X t) := by
    rw [hasFDerivAt_iff_isLittleO_nhds_zero] at hf_loc_hasFD_ℂ ⊢
    simp only [ContinuousLinearMap.coe_restrictScalars']
    exact hf_loc_hasFD_ℂ
  have hf_loc_diff_ℝ : DifferentiableAt ℝ f_loc (g_X t) :=
    hf_loc_hasFD_ℝ.differentiableAt
  have hf_loc_fderiv_ℝ : fderiv ℝ f_loc (g_X t) =
      (fderiv ℂ f_loc (g_X t)).restrictScalars ℝ :=
    hf_loc_hasFD_ℝ.fderiv
  have h_chain : fderiv ℝ (f_loc ∘ g_X) t =
      (fderiv ℝ f_loc (g_X t)).comp (fderiv ℝ g_X t) :=
    fderiv_comp t hf_loc_diff_ℝ hγ_diff
  have h_mfderiv : mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x) (γ t) =
      fderiv ℂ f_loc (g_X t) := by
    rw [hf_mdiff.mfderiv]
    rw [ModelWithCorners.range_eq_univ, fderivWithin_univ]
    congr 1
  have h_gY : (chartAt (H := ℂ) (((extChartAt 𝓘(ℂ, ℂ) x) ∘ γ) t)).toFun ∘
      ((extChartAt 𝓘(ℂ, ℂ) x) ∘ γ) = g_Y := rfl
  have hspeed_comp :
      Jacobians.Vendor.Kirov.pathSpeed ((extChartAt 𝓘(ℂ, ℂ) x) ∘ γ) t =
        mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x) (γ t)
          (Jacobians.Vendor.Kirov.pathSpeed γ t) := by
    rw [h_mfderiv]
    change fderiv ℝ ((chartAt (H := ℂ) (((extChartAt 𝓘(ℂ, ℂ) x) ∘ γ) t)).toFun ∘
        ((extChartAt 𝓘(ℂ, ℂ) x) ∘ γ)) t 1 =
      fderiv ℂ f_loc (g_X t) (Jacobians.Vendor.Kirov.pathSpeed γ t)
    rw [h_gY, h_eq.fderiv_eq, h_chain, ContinuousLinearMap.comp_apply,
      hf_loc_fderiv_ℝ, ContinuousLinearMap.coe_restrictScalars']
    rfl
  rw [← hspeed_comp]
  simp [Jacobians.Vendor.Kirov.pathSpeed]

namespace PathChartBallSubdivision

variable {P₀ P : X} {γ : Path P₀ P} (S : PathChartBallSubdivision γ)

/-- Integrability of the line-integrand on one flattened chart segment. -/
theorem chartFlatPath_lineIntegrable (n : ℕ) (form : HolomorphicOneForm X) :
    IntervalIntegrable
      (fun t : ℝ => (Jacobians.Bridge.bridgeForm form).toFun
        ((S.chartFlatPath n).extend t)
        (Jacobians.Vendor.Kirov.pathSpeed ((S.chartFlatPath n).extend) t))
      MeasureTheory.volume 0 1 := by
  let a : ℂ := (chartAt ℂ (S.chart n)) (γ (S.t n))
  let b : ℂ := (chartAt ℂ (S.chart n)) (γ (S.t (n + 1)))
  let g : ℝ → ℂ := fun t => form.coeff (S.chart n) (flatSegment a b t) *
    (fderiv ℝ (flatSegment a b) t (1 : ℝ))
  have hcoeff : ContinuousOn (fun t : ℝ => form.coeff (S.chart n) (flatSegment a b t))
      (Set.Icc (0 : ℝ) 1) := by
    exact (form.2.1 (S.chart n)).continuousOn.comp
      (continuous_flatSegment a b).continuousOn
      (fun t ht => by simpa [a, b] using S.flatSegment_mem_chart_target n ht)
  have hvel : Continuous (fun t : ℝ => fderiv ℝ (flatSegment a b) t (1 : ℝ)) := by
    have hcd : ContDiff ℝ (1 : ℕ∞ω) (flatSegment a b) := contDiff_flatSegment 1 a b
    have hpair : Continuous fun t : ℝ => (t, (1 : ℝ)) :=
      Continuous.prodMk continuous_id continuous_const
    simpa only [Function.comp_apply] using
      (hcd.continuous_fderiv_apply (by norm_num : (1 : ℕ∞ω) ≠ 0)).comp
        hpair
  have hg_cont : ContinuousOn g (Set.Icc (0 : ℝ) 1) := by
    exact hcoeff.mul hvel.continuousOn
  have hg_int : IntervalIntegrable g MeasureTheory.volume 0 1 :=
    ContinuousOn.intervalIntegrable_of_Icc zero_le_one hg_cont
  refine hg_int.congr_ae ?_
  filter_upwards
    [ae_restrict_mem (measurableSet_uIoc (a := (0 : ℝ)) (b := 1)),
      ae_restrict_of_ae
        (by simp [ae_iff, measure_singleton] :
          ∀ᵐ t : ℝ ∂MeasureTheory.volume, t ≠ 1)] with t htmem ht_ne_one
  have htIoc : t ∈ Set.Ioc (0 : ℝ) 1 := by
    simpa [Set.uIoc_of_le zero_le_one] using htmem
  have ht : t ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨htIoc.1, lt_of_le_of_ne htIoc.2 ht_ne_one⟩
  let y : X := (S.chartFlatPath n).extend t
  have hy_fixed : y ∈ (extChartAt 𝓘(ℂ, ℂ) (S.chart n)).source := by
    simpa [y, extChartAt_source] using
      S.chartFlatPath_extend_mem_chart_source_of_mem_Icc n ⟨ht.1.le, ht.2.le⟩
  have hy_self : y ∈ (extChartAt 𝓘(ℂ, ℂ) y).source := mem_extChartAt_source y
  letI : Nonempty X := ⟨y⟩
  have hswap : (Jacobians.Bridge.bridgeForm form).toFun y =
      BridgeForm.rawCLM form (S.chart n) y := by
    change BridgeForm.rawCLM form y y = BridgeForm.rawCLM form (S.chart n) y
    exact BridgeForm.rawCLM_swap_chart form hy_self hy_fixed
  have hspeed := mfderiv_extChartAt_apply_pathSpeed (x := S.chart n)
    (γ := (S.chartFlatPath n).extend) (t := t)
    ((Path.continuous_extend _).continuousAt)
    (S.chartFlatPath_chartAt_current_differentiableAt n t)
    hy_fixed
  have heq_flat : ((extChartAt 𝓘(ℂ, ℂ) (S.chart n)).toFun ∘
      (S.chartFlatPath n).extend) =ᶠ[𝓝 t] flatSegment a b := by
    simpa [a, b, extChartAt_coe, modelWithCornersSelf_coe] using
      S.chartFlatPath_chart_eventuallyEq_flatSegment_of_mem_Ioo n ht
  have hfixed_deriv :
      fderiv ℝ ((extChartAt 𝓘(ℂ, ℂ) (S.chart n)).toFun ∘
          (S.chartFlatPath n).extend) t (1 : ℝ) =
        fderiv ℝ (flatSegment a b) t (1 : ℝ) := by
    exact congrArg (fun L : ℝ →L[ℝ] ℂ => L (1 : ℝ)) heq_flat.fderiv_eq
  have hspeed_ext :
      (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) (S.chart n)) y)
          (Jacobians.Vendor.Kirov.pathSpeed ((S.chartFlatPath n).extend) t) =
        fderiv ℝ (flatSegment a b) t (1 : ℝ) := by
    simpa [y] using hspeed.trans hfixed_deriv
  have hcoord_chart :
      (chartAt ℂ (S.chart n)) y = flatSegment a b t := by
    have hpt := (S.chartFlatPath_chart_eventuallyEq_flatSegment_of_mem_Ioo n ht).self_of_nhds
    simpa [y, a, b] using hpt
  have hcoord_ext :
      (extChartAt 𝓘(ℂ, ℂ) (S.chart n)) y = flatSegment a b t := by
    simpa [extChartAt_coe, modelWithCornersSelf_coe] using hcoord_chart
  calc
    g t = (Jacobians.Bridge.bridgeForm form).toFun y
        (Jacobians.Vendor.Kirov.pathSpeed ((S.chartFlatPath n).extend) t) := by
      rw [hswap]
      unfold BridgeForm.rawCLM
      rw [hcoord_ext]
      have happly :
          (form.coeff (S.chart n) (flatSegment a b t) •
              mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) (S.chart n)) y)
              (Jacobians.Vendor.Kirov.pathSpeed ((S.chartFlatPath n).extend) t) =
            form.coeff (S.chart n) (flatSegment a b t) •
              ((mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) (S.chart n)) y)
                (Jacobians.Vendor.Kirov.pathSpeed ((S.chartFlatPath n).extend) t)) := by
        rfl
      refine Eq.trans ?_ happly.symm
      rw [hspeed_ext]
      rfl
    _ = (Jacobians.Bridge.bridgeForm form).toFun ((S.chartFlatPath n).extend t)
        (Jacobians.Vendor.Kirov.pathSpeed ((S.chartFlatPath n).extend) t) := rfl

end PathChartBallSubdivision

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
lemma pathTrans_extend_eq_kirov_concat
    {x y z : X} (γ₁ : Path x y) (γ₂ : Path y z) :
    (fun t : ℝ => (γ₁.trans γ₂).extend t) =
      Jacobians.Vendor.Kirov.concat γ₁.extend γ₂.extend := by
  funext t
  by_cases ht : t ≤ (1 / 2 : ℝ)
  · rw [Jacobians.Vendor.Kirov.concat_apply_left γ₁.extend γ₂.extend ht]
    exact Path.extend_trans_of_le_half γ₁ γ₂ ht
  · rw [Jacobians.Vendor.Kirov.concat_apply_right γ₁.extend γ₂.extend ht]
    exact Path.extend_trans_of_half_le γ₁ γ₂ (le_of_lt (not_le.mp ht))

/-- Integrability of Kirov's line-integrand is preserved by binary path concatenation. -/
theorem lineIntegrand_concat_intervalIntegrable
    (α : Jacobians.Vendor.Kirov.HolomorphicOneForms X)
    (γ₁ γ₂ : ℝ → X)
    (hγ₁ : IntervalIntegrable
      (fun t : ℝ => α.toFun (γ₁ t) (Jacobians.Vendor.Kirov.pathSpeed γ₁ t))
      MeasureTheory.volume 0 1)
    (hγ₂ : IntervalIntegrable
      (fun t : ℝ => α.toFun (γ₂ t) (Jacobians.Vendor.Kirov.pathSpeed γ₂ t))
      MeasureTheory.volume 0 1)
    (hγ₁diff : ∀ t : ℝ,
      DifferentiableAt ℝ ((chartAt (H := ℂ) (γ₁ t)).toFun ∘ γ₁) t)
    (hγ₂diff : ∀ t : ℝ,
      DifferentiableAt ℝ ((chartAt (H := ℂ) (γ₂ t)).toFun ∘ γ₂) t) :
    IntervalIntegrable
      (fun t : ℝ => α.toFun
        (Jacobians.Vendor.Kirov.concat γ₁ γ₂ t)
        (Jacobians.Vendor.Kirov.pathSpeed
          (Jacobians.Vendor.Kirov.concat γ₁ γ₂) t))
      MeasureTheory.volume 0 1 := by
  let f₁ : ℝ → ℂ := fun t =>
    α.toFun (γ₁ t) (Jacobians.Vendor.Kirov.pathSpeed γ₁ t)
  let f₂ : ℝ → ℂ := fun t =>
    α.toFun (γ₂ t) (Jacobians.Vendor.Kirov.pathSpeed γ₂ t)
  let f : ℝ → ℂ := fun t =>
    α.toFun (Jacobians.Vendor.Kirov.concat γ₁ γ₂ t)
      (Jacobians.Vendor.Kirov.pathSpeed
        (Jacobians.Vendor.Kirov.concat γ₁ γ₂) t)
  have hleft_base : IntervalIntegrable (fun t : ℝ => f₁ (2 * t))
      MeasureTheory.volume 0 (1 / 2 : ℝ) := by
    simpa [f₁] using hγ₁.comp_mul_left (c := (2 : ℝ))
  have hleft_scaled : IntervalIntegrable (fun t : ℝ => (2 : ℂ) * f₁ (2 * t))
      MeasureTheory.volume 0 (1 / 2 : ℝ) :=
    hleft_base.const_mul (2 : ℂ)
  have hleft : IntervalIntegrable f MeasureTheory.volume 0 (1 / 2 : ℝ) := by
    refine hleft_scaled.congr_ae ?_
    filter_upwards
      [ae_restrict_mem (measurableSet_uIoc (a := (0 : ℝ)) (b := (1 / 2 : ℝ))),
        ae_restrict_of_ae
          (by simp [ae_iff, measure_singleton] :
            ∀ᵐ t : ℝ ∂MeasureTheory.volume, t ≠ (1 / 2 : ℝ))] with t htmem ht_ne_half
    have htIoc : t ∈ Set.Ioc (0 : ℝ) (1 / 2 : ℝ) := by
      simpa [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] using htmem
    have htlt : t < (1 / 2 : ℝ) := lt_of_le_of_ne htIoc.2 ht_ne_half
    have hspeed := Jacobians.Vendor.Kirov.pathSpeed_concat_left γ₁ γ₂ t htlt
      (hγ₁diff (2 * t))
    have hpoint := Jacobians.Vendor.Kirov.concat_apply_left γ₁ γ₂ htlt.le
    calc
      (2 : ℂ) * f₁ (2 * t)
          = α.toFun (γ₁ (2 * t))
              (2 * Jacobians.Vendor.Kirov.pathSpeed γ₁ (2 * t)) := by
            dsimp [f₁]
            exact ((α.toFun (γ₁ (2 * t))).map_smul (2 : ℂ)
              (Jacobians.Vendor.Kirov.pathSpeed γ₁ (2 * t))).symm
      _ = f t := by
            dsimp [f]
            rw [hpoint, hspeed]
            rfl
  have hright_mul : IntervalIntegrable (fun t : ℝ => f₂ (2 * t))
      MeasureTheory.volume 0 (1 / 2 : ℝ) := by
    simpa [f₂] using hγ₂.comp_mul_left (c := (2 : ℝ))
  have hright_base : IntervalIntegrable (fun t : ℝ => f₂ (2 * t - 1))
      MeasureTheory.volume (1 / 2 : ℝ) 1 := by
    have htmp := hright_mul.comp_add_left (c := (-(1 / 2 : ℝ)))
    convert htmp using 1
    · ext t
      congr 1
      ring
    · norm_num
    · norm_num
  have hright_scaled : IntervalIntegrable (fun t : ℝ => (2 : ℂ) * f₂ (2 * t - 1))
      MeasureTheory.volume (1 / 2 : ℝ) 1 :=
    hright_base.const_mul (2 : ℂ)
  have hright : IntervalIntegrable f MeasureTheory.volume (1 / 2 : ℝ) 1 := by
    refine hright_scaled.congr_ae ?_
    filter_upwards
      [ae_restrict_mem (measurableSet_uIoc (a := (1 / 2 : ℝ)) (b := 1))] with t htmem
    have htIoc : t ∈ Set.Ioc (1 / 2 : ℝ) 1 := by
      rwa [Set.uIoc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at htmem
    have hspeed := Jacobians.Vendor.Kirov.pathSpeed_concat_right γ₁ γ₂ t htIoc.1
      (hγ₂diff (2 * t - 1))
    have hpoint := Jacobians.Vendor.Kirov.concat_apply_right γ₁ γ₂ (not_le.mpr htIoc.1)
    calc
      (2 : ℂ) * f₂ (2 * t - 1)
          = α.toFun (γ₂ (2 * t - 1))
              (2 * Jacobians.Vendor.Kirov.pathSpeed γ₂ (2 * t - 1)) := by
            dsimp [f₂]
            exact ((α.toFun (γ₂ (2 * t - 1))).map_smul (2 : ℂ)
              (Jacobians.Vendor.Kirov.pathSpeed γ₂ (2 * t - 1))).symm
      _ = f t := by
            dsimp [f]
            rw [hpoint, hspeed]
            rfl
  exact hleft.trans hright

namespace PathChartBallSubdivision

variable {P₀ P : X} {γ : Path P₀ P} (S : PathChartBallSubdivision γ)

/-- Integrability of the line-integrand along the first `k + 1` concatenated flat pieces. -/
theorem concatChartFlatPathAux_lineIntegrable (k : ℕ) (form : HolomorphicOneForm X) :
    IntervalIntegrable
      (fun t : ℝ => (Jacobians.Bridge.bridgeForm form).toFun
        ((S.concatChartFlatPathAux k).extend t)
        (Jacobians.Vendor.Kirov.pathSpeed ((S.concatChartFlatPathAux k).extend) t))
      MeasureTheory.volume 0 1 := by
  induction k with
  | zero =>
      simpa using S.chartFlatPath_lineIntegrable 0 form
  | succ k ih =>
      let γ₁ : ℝ → X := (S.concatChartFlatPathAux k).extend
      let γ₂ : ℝ → X := (S.chartFlatPath (k + 1)).extend
      have hpiece := S.chartFlatPath_lineIntegrable (k + 1) form
      have hconcat := lineIntegrand_concat_intervalIntegrable
        (α := Jacobians.Bridge.bridgeForm form) γ₁ γ₂ ih hpiece
        (fun t => by
          simpa [γ₁] using S.concatChartFlatPathAux_chartAt_current_differentiableAt k t)
        (fun t => by
          simpa [γ₂] using S.chartFlatPath_chartAt_current_differentiableAt (k + 1) t)
      have hpath :
          (fun t : ℝ => (S.concatChartFlatPathAux (k + 1)).extend t) =
            Jacobians.Vendor.Kirov.concat γ₁ γ₂ := by
        simpa [γ₁, γ₂, concatChartFlatPathAux_succ] using
          pathTrans_extend_eq_kirov_concat
            (S.concatChartFlatPathAux k) (S.chartFlatPath (k + 1))
      have hpath' :
          (S.concatChartFlatPathAux (k + 1)).extend =
            Jacobians.Vendor.Kirov.concat γ₁ γ₂ := by
        funext t
        exact congrFun hpath t
      rw [hpath']
      exact hconcat

/-- Integrability of the line-integrand along the full chart-flat bridge path. -/
theorem concatChartFlatPath_lineIntegrable (form : HolomorphicOneForm X) :
    IntervalIntegrable
      (fun t : ℝ => (Jacobians.Bridge.bridgeForm form).toFun
        ((S.concatChartFlatPath).extend t)
        (Jacobians.Vendor.Kirov.pathSpeed ((S.concatChartFlatPath).extend) t))
      MeasureTheory.volume 0 1 := by
  simpa [concatChartFlatPath] using
    S.concatChartFlatPathAux_lineIntegrable S.lastIndex form

end PathChartBallSubdivision

/-- **Integrability of the bridged line-integrand** along the chosen path.

For every holomorphic 1-form `form : HolomorphicOneForm X` and every
base pair `(P₀, P)`, the integrand `t ↦ (bridgeForm form)(γ t)(γ'(t))`
of `Vendor.Kirov.lineIntegral` along `γ := bridgePath P₀ P` is
interval-integrable on `[0, 1]`.

This is needed to invoke `Vendor.Kirov.lineIntegral_add`, which requires
integrability hypotheses for both summands. The concrete bridge path is
assembled from finitely many endpoint-flat chart segments: on each open
segment, chart-swapping rewrites the integrand as a continuous fixed-chart
expression, and the finitely many glue points are ignored by interval
integrability. -/
theorem bridgePath_lineIntegrable (P₀ P : X) (form : HolomorphicOneForm X) :
    IntervalIntegrable
      (fun t : ℝ => (Jacobians.Bridge.bridgeForm form).toFun
        (bridgePath (X := X) P₀ P t)
        (Jacobians.Vendor.Kirov.pathSpeed (bridgePath (X := X) P₀ P) t))
      MeasureTheory.volume 0 1 := by
  let γ : Path P₀ P := (exists_path P₀ P).some
  let S : PathChartBallSubdivision γ := (exists_pathChartBallSubdivision γ).some
  change IntervalIntegrable
    (fun t : ℝ => (Jacobians.Bridge.bridgeForm form).toFun
      ((S.concatChartFlatPath).extend t)
      (Jacobians.Vendor.Kirov.pathSpeed ((S.concatChartFlatPath).extend) t))
    MeasureTheory.volume 0 1
  exact S.concatChartFlatPath_lineIntegrable form

/-! ## ChartLine — concrete affine path in chart coordinates

The straight line from `(extChartAt P) P` to `z` in the chart at `P`,
pulled back through `(extChartAt P).symm`. This is the concrete path
whose FTC we can derive directly from Mathlib + Kirov primitives, with
no further structural axioms.

Used inside the proof of `kirovBackedFunctional_local_antiderivative`
once we connect `bridgePath` to a chart-line concatenation near each
endpoint. -/

/-- The straight line in chart coordinates from `(extChartAt P) P` to `z`,
pulled back through `(extChartAt P).symm`. -/
noncomputable def chartLine (P : X) (z : ℂ) : ℝ → X :=
  fun t => (extChartAt 𝓘(ℂ, ℂ) P).symm ((1 - t) • (extChartAt 𝓘(ℂ, ℂ) P) P + t • z)

@[simp] theorem chartLine_at_zero (P : X) (z : ℂ) :
    chartLine (X := X) P z 0 = P := by
  simp [chartLine]

@[simp] theorem chartLine_at_one (P : X) (z : ℂ) :
    chartLine (X := X) P z 1 = (extChartAt 𝓘(ℂ, ℂ) P).symm z := by
  simp [chartLine]

/-! ### Reduction lemmas for `chartLine`

The `chartLine_FTC` proof factors through six small lemmas:

* `extChartAt_chartLine` — chart image of `chartLine P z t` is the affine
  line `(1 - t) • (extChartAt P) P + t • z`.
* `pathSpeed_extChartAt_chartLine` — derivative of that affine line is
  the constant `z - (extChartAt P) P`.
* `mfderiv_extChartAt_pathSpeed_chartLine` — combining the above with
  `Vendor.Kirov.pathSpeed_comp_eq_mfderiv`.
* `bridgeForm_chartLine_integrand` — combining `rawCLM_swap_chart`
  (chart-swap to fixed chart at `P`) with the above to get the integrand
  in closed form `(form.coeff P (1 - t) • a + t • z) * (z - a)`.
* `lineIntegral_chartLine_eq` — change of variable `u = a + t (z - a)`
  reduces the line integral to `∫_a^z form.coeff P u du`.
* `chartLine_FTC` — `intervalIntegral.integral_hasDerivAt_right` plus
  continuity of `form.coeff P` (from `IsHolomorphicOneFormCoeff`). -/

/-- Chart image of the chart-line: an affine line in ℂ from
`(extChartAt P) P` to `z`, parameterized by `t ∈ [0, 1]`. -/
theorem extChartAt_chartLine (P : X) (z : ℂ) {t : ℝ}
    (hz : (1 - t) • (extChartAt 𝓘(ℂ, ℂ) P) P + t • z ∈
      (extChartAt 𝓘(ℂ, ℂ) P).target) :
    (extChartAt 𝓘(ℂ, ℂ) P) (chartLine (X := X) P z t) =
      (1 - t) • (extChartAt 𝓘(ℂ, ℂ) P) P + t • z := by
  exact (extChartAt 𝓘(ℂ, ℂ) P).right_inv hz

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
private lemma chartLine_continuousAt_of_mem_target (P : X) (z : ℂ) {t : ℝ}
    (hz : (1 - t) • (extChartAt 𝓘(ℂ, ℂ) P) P + t • z ∈
      (extChartAt 𝓘(ℂ, ℂ) P).target) :
    ContinuousAt (chartLine (X := X) P z) t := by
  let η : ℝ → ℂ := fun s =>
    (1 - s) • (extChartAt 𝓘(ℂ, ℂ) P) P + s • z
  have hOpen : IsOpen (extChartAt 𝓘(ℂ, ℂ) P).target := by
    rw [extChartAt_target]
    simp [(chartAt ℂ P).open_target]
  have hsymm_cont :
      ContinuousAt ((extChartAt 𝓘(ℂ, ℂ) P).symm : ℂ → X) (η t) := by
    exact (continuousOn_extChartAt_symm P).continuousAt
      (hOpen.mem_nhds (by simpa [η] using hz))
  have hη_cont : ContinuousAt η t := by
    dsimp [η]
    fun_prop
  have hcomp :
      ContinuousAt (((extChartAt 𝓘(ℂ, ℂ) P).symm : ℂ → X) ∘ η) t :=
    hsymm_cont.comp hη_cont
  change ContinuousAt
    (fun s : ℝ =>
      (extChartAt 𝓘(ℂ, ℂ) P).symm
        ((1 - s) • (extChartAt 𝓘(ℂ, ℂ) P) P + s • z)) t
  simpa [η, Function.comp_def] using hcomp

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
private lemma chartLine_current_chart_differentiableAt (P : X) (z : ℂ) {t : ℝ}
    (hz : (1 - t) • (extChartAt 𝓘(ℂ, ℂ) P) P + t • z ∈
      (extChartAt 𝓘(ℂ, ℂ) P).target) :
    DifferentiableAt ℝ
      ((chartAt (H := ℂ) (chartLine (X := X) P z t)).toFun ∘
        chartLine (X := X) P z) t := by
  let w : ℂ := (1 - t) • (extChartAt 𝓘(ℂ, ℂ) P) P + t • z
  let y : X := chartLine (X := X) P z t
  have hy_eq : y = (extChartAt 𝓘(ℂ, ℂ) P).symm w := by
    simp [y, w, chartLine]
  have htrans_diff_C : DifferentiableAt ℂ
      ((extChartAt 𝓘(ℂ, ℂ) y) ∘ (extChartAt 𝓘(ℂ, ℂ) P).symm) w := by
    have hsymm_mdiff_within : MDifferentiableWithinAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
        (extChartAt 𝓘(ℂ, ℂ) P).symm (Set.range (𝓘(ℂ, ℂ))) w := by
      simpa [w] using mdifferentiableWithinAt_extChartAt_symm hz
    have hsymm_mdiff : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
        (extChartAt 𝓘(ℂ, ℂ) P).symm w := by
      have hrange :
          (Set.range (𝓘(ℂ, ℂ) : ModelWithCorners ℂ ℂ ℂ)) = Set.univ :=
        ModelWithCorners.range_eq_univ _
      rw [← mdifferentiableWithinAt_univ, ← hrange]
      exact hsymm_mdiff_within
    have hchart_mdiff : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
        (extChartAt 𝓘(ℂ, ℂ) y) ((extChartAt 𝓘(ℂ, ℂ) P).symm w) := by
      apply mdifferentiableAt_extChartAt
      rw [← extChartAt_source (I := 𝓘(ℂ, ℂ)), ← hy_eq]
      exact mem_extChartAt_source y
    exact (hchart_mdiff.comp w hsymm_mdiff).differentiableAt
  have htrans_diff_R : DifferentiableAt ℝ
      ((extChartAt 𝓘(ℂ, ℂ) y) ∘ (extChartAt 𝓘(ℂ, ℂ) P).symm) w :=
    htrans_diff_C.restrictScalars ℝ
  have haff : DifferentiableAt ℝ
      (fun s : ℝ => (1 - s) • (extChartAt 𝓘(ℂ, ℂ) P) P + s • z) t := by
    fun_prop
  have hcomp := htrans_diff_R.comp t haff
  simpa [chartLine, y, w, extChartAt_coe, modelWithCornersSelf_coe,
    Function.comp_def] using hcomp

private lemma pathSpeed_extChartAt_chartLine (P : X) (z : ℂ) {t : ℝ}
    (hz : (1 - t) • (extChartAt 𝓘(ℂ, ℂ) P) P + t • z ∈
      (extChartAt 𝓘(ℂ, ℂ) P).target) :
    fderiv ℝ ((extChartAt 𝓘(ℂ, ℂ) P).toFun ∘ chartLine (X := X) P z)
        t (1 : ℝ) =
      z - (extChartAt 𝓘(ℂ, ℂ) P) P := by
  let a : ℂ := (extChartAt 𝓘(ℂ, ℂ) P) P
  let η : ℝ → ℂ := fun s => (1 - s) • a + s • z
  have hOpen : IsOpen (extChartAt 𝓘(ℂ, ℂ) P).target := by
    rw [extChartAt_target]
    simp [(chartAt ℂ P).open_target]
  have hη_cont : ContinuousAt η t := by
    dsimp [η]
    fun_prop
  have hη_target : ∀ᶠ s in 𝓝 t, η s ∈ (extChartAt 𝓘(ℂ, ℂ) P).target :=
    hη_cont.eventually (hOpen.mem_nhds (by simpa [η, a] using hz))
  have heq :
      ((extChartAt 𝓘(ℂ, ℂ) P).toFun ∘ chartLine (X := X) P z) =ᶠ[𝓝 t]
        η := by
    filter_upwards [hη_target] with s hs
    exact extChartAt_chartLine (X := X) P z (by simpa [η, a] using hs)
  have hder : fderiv ℝ η t (1 : ℝ) = z - a := by
    have hder' : HasDerivAt (fun s : ℝ => a + s • (z - a)) (z - a) t := by
      simpa only [Pi.add_apply, zero_add, one_smul, id_eq] using
        (hasDerivAt_const (x := t) (c := a)).add
          ((hasDerivAt_id t).smul_const (z - a))
    have hfun : (fun s : ℝ => (1 - s) • a + s • z) =
        fun s : ℝ => a + s • (z - a) := by
      funext s
      rw [sub_smul, one_smul]
      module
    exact (hder'.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq hfun)).deriv
  simpa [a] using
    (congrArg (fun L : ℝ →L[ℝ] ℂ => L (1 : ℝ)) heq.fderiv_eq).trans hder

private lemma mfderiv_extChartAt_pathSpeed_chartLine [Nonempty X]
    (P : X) (z : ℂ) {t : ℝ}
    (hz : (1 - t) • (extChartAt 𝓘(ℂ, ℂ) P) P + t • z ∈
      (extChartAt 𝓘(ℂ, ℂ) P).target) :
    (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) P)
        (chartLine (X := X) P z t))
      (Jacobians.Vendor.Kirov.pathSpeed (chartLine (X := X) P z) t) =
      z - (extChartAt 𝓘(ℂ, ℂ) P) P := by
  have hspeed := mfderiv_extChartAt_apply_pathSpeed (x := P)
    (γ := chartLine (X := X) P z) (t := t)
    (chartLine_continuousAt_of_mem_target (X := X) P z hz)
    (chartLine_current_chart_differentiableAt (X := X) P z hz)
    (by
      have hsrc := (extChartAt 𝓘(ℂ, ℂ) P).map_target hz
      simpa [chartLine] using hsrc)
  exact hspeed.trans (pathSpeed_extChartAt_chartLine (X := X) P z hz)

private lemma bridgeForm_chartLine_integrand [Nonempty X]
    (P : X) (form : HolomorphicOneForm X) (z : ℂ) {t : ℝ}
    (hz : (1 - t) • (extChartAt 𝓘(ℂ, ℂ) P) P + t • z ∈
      (extChartAt 𝓘(ℂ, ℂ) P).target) :
    (Jacobians.Bridge.bridgeForm form).toFun (chartLine (X := X) P z t)
      (Jacobians.Vendor.Kirov.pathSpeed (chartLine (X := X) P z) t) =
      form.coeff P ((1 - t) • (extChartAt 𝓘(ℂ, ℂ) P) P + t • z) *
        (z - (extChartAt 𝓘(ℂ, ℂ) P) P) := by
  let y : X := chartLine (X := X) P z t
  have hy_self : y ∈ (extChartAt 𝓘(ℂ, ℂ) y).source := mem_extChartAt_source y
  have hy_fixed : y ∈ (extChartAt 𝓘(ℂ, ℂ) P).source := by
    have hsrc := (extChartAt 𝓘(ℂ, ℂ) P).map_target hz
    simpa [y, chartLine] using hsrc
  have hswap : (Jacobians.Bridge.bridgeForm form).toFun y =
      BridgeForm.rawCLM form P y := by
    change BridgeForm.rawCLM form y y = BridgeForm.rawCLM form P y
    exact BridgeForm.rawCLM_swap_chart form hy_self hy_fixed
  have hcoord :
      (extChartAt 𝓘(ℂ, ℂ) P) y =
        (1 - t) • (extChartAt 𝓘(ℂ, ℂ) P) P + t • z := by
    simpa [y] using extChartAt_chartLine (X := X) P z hz
  have hspeed :
      (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) P) y)
        (Jacobians.Vendor.Kirov.pathSpeed (chartLine (X := X) P z) t) =
        z - (extChartAt 𝓘(ℂ, ℂ) P) P := by
    simpa [y] using mfderiv_extChartAt_pathSpeed_chartLine (X := X) P z hz
  calc
    (Jacobians.Bridge.bridgeForm form).toFun (chartLine (X := X) P z t)
        (Jacobians.Vendor.Kirov.pathSpeed (chartLine (X := X) P z) t)
        = BridgeForm.rawCLM form P y
            (Jacobians.Vendor.Kirov.pathSpeed (chartLine (X := X) P z) t) := by
          rw [hswap]
    _ = form.coeff P ((1 - t) • (extChartAt 𝓘(ℂ, ℂ) P) P + t • z) *
        (z - (extChartAt 𝓘(ℂ, ℂ) P) P) := by
          unfold BridgeForm.rawCLM
          rw [hcoord]
          change form.coeff P
              ((1 - t) • (extChartAt 𝓘(ℂ, ℂ) P) P + t • z) •
              ((mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
                (extChartAt 𝓘(ℂ, ℂ) P) y)
                (Jacobians.Vendor.Kirov.pathSpeed (chartLine (X := X) P z) t)) =
            form.coeff P
              ((1 - t) • (extChartAt 𝓘(ℂ, ℂ) P) P + t • z) *
              (z - (extChartAt 𝓘(ℂ, ℂ) P) P)
          rw [hspeed]
          rfl

private lemma lineIntegral_chartLine_eq_eventually [Nonempty X]
    (P : X) (form : HolomorphicOneForm X) :
    (fun z : ℂ =>
        Jacobians.Vendor.Kirov.lineIntegral (Jacobians.Bridge.bridgeForm form)
          (chartLine (X := X) P z)) =ᶠ[𝓝 ((extChartAt 𝓘(ℂ, ℂ) P) P)]
      (fun z : ℂ =>
        ∫ t in (0 : ℝ)..1,
          form.coeff P ((1 - t) • (extChartAt 𝓘(ℂ, ℂ) P) P + t • z) *
            (z - (extChartAt 𝓘(ℂ, ℂ) P) P)) := by
  let a : ℂ := (extChartAt 𝓘(ℂ, ℂ) P) P
  have ha_target : a ∈ (extChartAt 𝓘(ℂ, ℂ) P).target := by
    simp [a]
  have hOpen : IsOpen (extChartAt 𝓘(ℂ, ℂ) P).target := by
    rw [extChartAt_target]
    simp [(chartAt ℂ P).open_target]
  rcases Metric.isOpen_iff.mp hOpen a ha_target with ⟨r, hr_pos, hr_sub⟩
  filter_upwards [Metric.ball_mem_nhds a hr_pos] with z hz_ball
  unfold Jacobians.Vendor.Kirov.lineIntegral
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [Set.uIcc_of_le zero_le_one] using ht
  have hline :
      (1 - t) • a + t • z ∈ segment ℝ a z := by
    rw [← AffineMap.lineMap_apply_module]
    exact lineMap_mem_segment ℝ a z htIcc
  have htarget :
      (1 - t) • (extChartAt 𝓘(ℂ, ℂ) P) P + t • z ∈
        (extChartAt 𝓘(ℂ, ℂ) P).target := by
    have hball : (1 - t) • a + t • z ∈ Metric.ball a r :=
      segment_subset_ball (Metric.mem_ball_self hr_pos) hz_ball hline
    exact hr_sub (by simpa [a] using hball)
  exact bridgeForm_chartLine_integrand (X := X) P form z htarget

private lemma hasDerivAt_mul_sub_of_continuousAt {f : ℂ → ℂ} {a : ℂ}
    (hf : ContinuousAt f a) :
    HasDerivAt (fun z : ℂ => f z * (z - a)) (f a) a := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hslope :
      (slope (fun z : ℂ => f z * (z - a)) a) =ᶠ[𝓝[≠] a] f := by
    have hfun :
        (fun z : ℂ => f z * (z - a)) = fun z : ℂ => (z - a) • f z := by
      funext z
      simp [smul_eq_mul, mul_comm]
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hne : a ≠ z := by
      simpa [Set.mem_compl_iff, Set.mem_singleton_iff, eq_comm] using hz
    rw [hfun]
    exact slope_sub_smul f hne
  exact Tendsto.congr' hslope.symm (hf.tendsto.mono_left nhdsWithin_le_nhds)

lemma chartLine_average_coeff_continuousAt
    (P : X) (form : HolomorphicOneForm X) :
    ContinuousAt
      (fun z : ℂ =>
        ∫ t in (0 : ℝ)..1,
          form.coeff P ((1 - t) • (extChartAt 𝓘(ℂ, ℂ) P) P + t • z))
      ((extChartAt 𝓘(ℂ, ℂ) P) P) := by
  let a : ℂ := (extChartAt 𝓘(ℂ, ℂ) P) P
  have ha_target : a ∈ (extChartAt 𝓘(ℂ, ℂ) P).target := by
    simp [a]
  have hOpen : IsOpen (extChartAt 𝓘(ℂ, ℂ) P).target := by
    rw [extChartAt_target]
    simp [(chartAt ℂ P).open_target]
  have hcoeff_cont :
      ContinuousOn (form.coeff P) (extChartAt 𝓘(ℂ, ℂ) P).target :=
    (form.2.1 P).continuousOn
  have hcoeff_at : ContinuousAt (form.coeff P) a := by
    have hcoeff_an :
        AnalyticAt ℂ (form.coeff P) a :=
      (form.2.1 P).analyticAt (hOpen.mem_nhds ha_target)
    exact hcoeff_an.continuousAt
  rcases Metric.isOpen_iff.mp hOpen a ha_target with ⟨r, hr_pos, hr_sub⟩
  let ρ : ℝ := r / 2
  have hρ_pos : 0 < ρ := by
    positivity
  have hρ_lt_r : ρ < r := by
    dsimp [ρ]
    linarith
  have hseg_target :
      ∀ z ∈ Metric.closedBall a ρ, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        (1 - t) • a + t • z ∈ (extChartAt 𝓘(ℂ, ℂ) P).target := by
    intro z hz t ht
    have hz_ball : z ∈ Metric.ball a r := by
      have hdist_lt : dist z a < r := by
        exact lt_of_le_of_lt (by simpa [Metric.mem_closedBall] using hz) hρ_lt_r
      simpa [Metric.mem_ball] using hdist_lt
    have hline :
        (1 - t) • a + t • z ∈ segment ℝ a z := by
      rw [← AffineMap.lineMap_apply_module]
      exact lineMap_mem_segment ℝ a z ht
    have hball : (1 - t) • a + t • z ∈ Metric.ball a r :=
      segment_subset_ball (Metric.mem_ball_self hr_pos) hz_ball hline
    exact hr_sub hball
  have hprod_cont :
      ContinuousOn
        (fun p : ℂ × ℝ => form.coeff P ((1 - p.2) • a + p.2 • p.1))
        (Metric.closedBall a ρ ×ˢ Set.Icc (0 : ℝ) 1) := by
    have haff_cont :
        Continuous fun p : ℂ × ℝ => (1 - p.2) • a + p.2 • p.1 := by
      fun_prop
    exact hcoeff_cont.comp haff_cont.continuousOn
      (fun p hp => hseg_target p.1 hp.1 p.2 hp.2)
  have hcompact :
      IsCompact (Metric.closedBall a ρ ×ˢ Set.Icc (0 : ℝ) 1) :=
    (isCompact_closedBall a ρ).prod isCompact_Icc
  rcases hcompact.exists_bound_of_continuousOn hprod_cont with ⟨M, hM⟩
  have hF_meas :
      ∀ᶠ z in 𝓝 a,
        AEStronglyMeasurable
          (fun t : ℝ => form.coeff P ((1 - t) • a + t • z))
          (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
    filter_upwards [Metric.ball_mem_nhds a hρ_pos] with z hz
    have hz_closed : z ∈ Metric.closedBall a ρ :=
      Metric.ball_subset_closedBall hz
    have hcont_t :
        ContinuousOn
          (fun t : ℝ => form.coeff P ((1 - t) • a + t • z))
          (Set.Icc (0 : ℝ) 1) := by
      have haff_cont : Continuous fun t : ℝ => (1 - t) • a + t • z := by
        fun_prop
      exact hcoeff_cont.comp haff_cont.continuousOn
        (fun t ht => hseg_target z hz_closed t ht)
    have huIoc_subset : Set.uIoc (0 : ℝ) 1 ⊆ Set.Icc (0 : ℝ) 1 := by
      rw [Set.uIoc_of_le zero_le_one]
      exact Set.Ioc_subset_Icc_self
    exact hcont_t.aestronglyMeasurable_of_subset_isCompact
      isCompact_Icc measurableSet_uIoc huIoc_subset
  have h_bound :
      ∀ᶠ z in 𝓝 a,
        ∀ᵐ t ∂MeasureTheory.volume,
          t ∈ Set.uIoc (0 : ℝ) 1 →
            ‖form.coeff P ((1 - t) • a + t • z)‖ ≤ max M 0 := by
    filter_upwards [Metric.ball_mem_nhds a hρ_pos] with z hz
    have hz_closed : z ∈ Metric.closedBall a ρ :=
      Metric.ball_subset_closedBall hz
    filter_upwards with t
    intro ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := by
      have htIoc : t ∈ Set.Ioc (0 : ℝ) 1 := by
        simpa [Set.uIoc_of_le zero_le_one] using ht
      exact Set.Ioc_subset_Icc_self htIoc
    exact (hM (z, t) ⟨hz_closed, htIcc⟩).trans (le_max_left M 0)
  have h_bound_int :
      IntervalIntegrable (fun _ : ℝ => max M 0) MeasureTheory.volume (0 : ℝ) 1 := by
    exact intervalIntegrable_const
  have h_cont :
      ∀ᵐ t ∂MeasureTheory.volume,
        t ∈ Set.uIoc (0 : ℝ) 1 →
          ContinuousAt
            (fun z : ℂ => form.coeff P ((1 - t) • a + t • z)) a := by
    filter_upwards with t
    intro _ht
    have hline_at : (1 - t) • a + t • a = a := by
      rw [← add_smul]
      ring_nf
      simp
    have haff_cont : ContinuousAt (fun z : ℂ => (1 - t) • a + t • z) a := by
      fun_prop
    have hcomp :
        ContinuousAt
          ((form.coeff P) ∘ fun z : ℂ => (1 - t) • a + t • z) a :=
      ContinuousAt.comp_of_eq
        (f := fun z : ℂ => (1 - t) • a + t • z)
        (g := form.coeff P) (x := a) (y := a)
        hcoeff_at haff_cont hline_at
    simpa [Function.comp_def] using hcomp
  simpa [a] using
    (intervalIntegral.continuousAt_of_dominated_interval
      (μ := MeasureTheory.volume)
      (F := fun z : ℂ => fun t : ℝ =>
        form.coeff P ((1 - t) • a + t • z))
      (x₀ := a) (bound := fun _ : ℝ => max M 0)
      (a := (0 : ℝ)) (b := 1) hF_meas h_bound h_bound_int h_cont)

/-- **FTC for `chartLine`.** The line integral of `bridgeForm form` along
the chart-line from `P` to `(extChartAt P).symm z` has derivative w.r.t.
`z` equal to `form.coeff P ((extChartAt P) P)` at `z = (extChartAt P) P`.

Derivation (genuine, no extra axioms): see the six reduction lemmas
above. -/
theorem chartLine_FTC [Nonempty X] (P : X) (form : HolomorphicOneForm X) :
    HasDerivAt
      (fun z : ℂ =>
        Jacobians.Vendor.Kirov.lineIntegral (Jacobians.Bridge.bridgeForm form)
          (chartLine (X := X) P z))
      (form.coeff P ((extChartAt 𝓘(ℂ, ℂ) P) P))
      ((extChartAt 𝓘(ℂ, ℂ) P) P) := by
  have hline := lineIntegral_chartLine_eq_eventually (X := X) P form
  suffices hparam :
      HasDerivAt
        (fun z : ℂ =>
          ∫ t in (0 : ℝ)..1,
            form.coeff P ((1 - t) • (extChartAt 𝓘(ℂ, ℂ) P) P + t • z) *
              (z - (extChartAt 𝓘(ℂ, ℂ) P) P))
        (form.coeff P ((extChartAt 𝓘(ℂ, ℂ) P) P))
        ((extChartAt 𝓘(ℂ, ℂ) P) P) by
    exact hparam.congr_of_eventuallyEq hline
  let a : ℂ := (extChartAt 𝓘(ℂ, ℂ) P) P
  let I : ℂ → ℂ := fun z =>
    ∫ t in (0 : ℝ)..1, form.coeff P ((1 - t) • a + t • z)
  have hIcont : ContinuousAt I a := by
    simpa [I, a] using chartLine_average_coeff_continuousAt (X := X) P form
  have hIa : I a = form.coeff P a := by
    calc
      I a = ∫ _t in (0 : ℝ)..1, form.coeff P a := by
        apply intervalIntegral.integral_congr
        intro t _ht
        change form.coeff P ((1 - t) • a + t • a) = form.coeff P a
        congr 1
        rw [← add_smul]
        ring_nf
        simp
      _ = form.coeff P a := by
        simp
  have hder :
      HasDerivAt (fun z : ℂ => I z * (z - a)) (form.coeff P a) a := by
    simpa [hIa] using hasDerivAt_mul_sub_of_continuousAt hIcont
  simpa [I, a] using hder

/-! ## The bridge functional

Given the path-selection axioms and `bridgeForm`, we can define our
`pathIntegralBasepointFunctional` shape via `Vendor.Kirov.lineIntegral`. -/

/-- **The Kirov-backed path integral functional.** Computes
`∫_{P₀}^P ω` by:
1. choosing a smooth path `γ := bridgePath P₀ P` from `P₀` to `P`;
2. converting `ω : HolomorphicOneForm X` to a `ContMDiffSection` via
   `bridgeForm`;
3. applying `Vendor.Kirov.lineIntegral` to the section + path.

Linearity in `ω` follows from `lineIntegral_add` / `lineIntegral_smul`
and the linearity of `bridgeForm`.

This **shape-matches** our axiom `pathIntegralBasepointFunctional`. -/
noncomputable def kirovBackedFunctional (P₀ P : X) :
    HolomorphicOneForm X →ₗ[ℂ] ℂ where
  toFun form :=
    Jacobians.Vendor.Kirov.lineIntegral
      (Jacobians.Bridge.bridgeForm form)
      (bridgePath (X := X) P₀ P)
  map_add' form₁ form₂ := by
    -- Use `bridgeForm.map_add'` to push `+` through `bridgeForm`, then
    -- `lineIntegral_add` (under the integrability axioms) to split the integral.
    have hBF : Jacobians.Bridge.bridgeForm (form₁ + form₂) =
        Jacobians.Bridge.bridgeForm form₁ + Jacobians.Bridge.bridgeForm form₂ :=
      LinearMap.map_add _ form₁ form₂
    rw [hBF]
    exact Jacobians.Vendor.Kirov.lineIntegral_add _ _ _
      (bridgePath_lineIntegrable P₀ P form₁) (bridgePath_lineIntegrable P₀ P form₂)
  map_smul' c form := by
    -- Use `bridgeForm.map_smul'` to push `c • ·` through `bridgeForm`, then
    -- `lineIntegral_smul` to extract the scalar (no integrability hypothesis needed).
    have hBF : Jacobians.Bridge.bridgeForm (c • form) =
        c • Jacobians.Bridge.bridgeForm form :=
      LinearMap.map_smul _ c form
    rw [hBF]
    exact Jacobians.Vendor.Kirov.lineIntegral_smul c _ _

/-! ## The single-valued ℂ FTC is FALSE — removed 2026-06-04

A former `theorem kirovBackedFunctional_local_antiderivative` (a `sorry`,
the bridge-side mirror of `AX_pathIntegral_local_antiderivative`) asserted

```
HasDerivAt (fun z => kirovBackedFunctional P₀ ((extChartAt P).symm z) form)
           (form.coeff P (φ P)) (φ P)        -- for every P
```

This is **false on any genus ≥ 1 curve.** `kirovBackedFunctional P₀ · form` is
a single-valued `ℂ`-valued function of its endpoint; the statement, quantified
over all `P`, makes it a *global primitive* of the holomorphic 1-form `form`,
forcing every period `∮_γ form = 0` — contradicting nonzero periods (e.g.
`genus_Elliptic = 1`). No chart-line-tail refinement of `bridgePath` can prove
it; the obstruction is not a missing construction but the falsity of the goal.
(A prior attempt "closed" the `sorry` by relabelling it as a fresh axiom; that
was reverted. The deeper reason it cannot be discharged honestly is that it is
false.)

**The honest architecture:**
* `kirovBackedFunctional` (the `def` above) is a fine, genuine line-integral
  `def` — it can replace the *opaque* axiom `pathIntegralBasepointFunctional`
  in `Axioms/AbelJacobiMap.lean`, de-opaquing `ofCurve` (killing the
  zero-functional degeneracy) **with no FTC required.** That replacement is
  sound; only the FTC theorem above was false.
* Path-independence lives — correctly — at the **closed-loop / homology**
  level, as the (true, standard) axiom
  `Jacobians.RiemannSurface.loopIntegralToH1` (`∮_γ ω` depends only on
  `[γ] ∈ H₁`). Its honest discharge globalizes the chart-local homotopy
  invariance now in `Jacobians.Bridge.ContourDeformation`
  (`contourDeformation1D_pathHomotopy_abstract`) via a homotopy-rectangle
  subdivision. See `docs/planning/ABEL_JACOBI_DISCHARGE_PLAN.md`.
* A genuine "FTC", if ever wanted, must be stated on the **quotient**
  `ofCurve : X → ℂ^g/Λ` (manifold-differentiable; the period ambiguity is
  locally constant), not on a single-valued ℂ lift. -/

end Jacobians.Bridge
