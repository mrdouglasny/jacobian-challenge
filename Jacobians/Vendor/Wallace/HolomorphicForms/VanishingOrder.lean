/-
Copyright (c) 2026 Michal J Wallace. All rights reserved.
Released under the MIT license (the upstream repository LICENSE; © Michal J Wallace).
Original source: https://github.com/tangentstorm/JacobianChallenge
                 Jacobian/HolomorphicForms/VanishingOrder.lean (commit 82349bc8, 2026-06-01).
Note: the upstream repo LICENSE is MIT; on full adoption, vendor the upstream
LICENSE under `vendor/wallace-jacobian-challenge/`.

Vendored (trial) into this repository on 2026-06-02 by Michael R Douglas.
Modifications relative to upstream:
- Renamespaced under `Jacobians.Vendor.Wallace.HolomorphicForms.*`.
- Internal imports retargeted to the vendored module paths.
No mathematical content was altered.
-/

import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt

/-!
# Order of vanishing of a meromorphic germ at a point on a complex 1-manifold

This file formalizes blueprint leaf node `def:vanishing-order` from
`tex/sections/01-compact-riemann-surfaces.tex`:

> For a holomorphic chart `φ : U → ℂ` sending `p ↦ 0` and a meromorphic germ
> `f` at `p`, the order of vanishing `ord_p(f) ∈ ℤ ∪ {+∞}` is the order of
> the Laurent series of `f ∘ φ⁻¹` at `0`. The convention is `ord_p(0) = +∞`
> and `ord_p(f) < 0` for poles. The value is independent of the chart.

The construction uses Mathlib's `meromorphicOrderAt` for `ℂ → ℂ` functions,
pulled back through the canonical extended chart `extChartAt 𝓘(ℂ) p`.
Chart independence is the substantive content.

## Main definitions

* `MeromorphicAtX f p` : `f : X → ℂ` is meromorphic at `p` in the manifold
  sense, i.e. its pullback to ℂ via the canonical extended chart at `p` is
  meromorphic in the usual sense.
* `orderAt p f : WithTop ℤ` : the order of vanishing of `f` at `p`,
  computed in the canonical extended chart. Returns `0` (junk) if `f` is
  not meromorphic at `p`, and `⊤` if `f` vanishes locally near `p`.

## Main theorems

* `orderAt_eq_meromorphicOrderAt_of_mem_maximalAtlas` — chart
  independence: for any chart `e ∈ maximalAtlas 𝓘(ℂ) ω X` with
  `p ∈ e.source`, `orderAt p f` equals `meromorphicOrderAt (f ∘ e.symm)
  (e p)`.

## TOPDOWN refinement

The chart-independence theorem reduces to two sub-obligations about
the transition map `g := chartAt ℂ p ∘ e.symm`:
-/

set_option linter.style.longLine false
set_option linter.style.show false
set_option linter.style.emptyLine false
set_option linter.unusedSectionVars false

namespace Jacobians.Vendor.Wallace.HolomorphicForms.VanishingOrder

open scoped Manifold Topology ContDiff
open Set Filter

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-!
### Definitions

`MeromorphicAtX` and `orderAt` are introduced before the analytic-manifold
hypothesis is needed: their definitions only use the `ChartedSpace ℂ X`
structure and the canonical extended chart `extChartAt 𝓘(ℂ) p`.
-/

/--
`f : X → ℂ` is meromorphic at `p ∈ X` (in the manifold sense) iff its
pullback `f ∘ (extChartAt 𝓘(ℂ) p).symm` is meromorphic at `extChartAt 𝓘(ℂ) p p`
in the usual `ℂ → ℂ` sense.

Wraps Mathlib's `MeromorphicAt`, which is only defined for `f : 𝕜 → E`.
-/
def MeromorphicAtX (f : X → ℂ) (p : X) : Prop :=
  MeromorphicAt (f ∘ (extChartAt 𝓘(ℂ) p).symm) (extChartAt 𝓘(ℂ) p p)

/--
The order of vanishing of a meromorphic germ `f : X → ℂ` at `p ∈ X`.

Computed in the canonical extended chart at `p`. Returns:
* a finite integer `n ∈ ℤ` for a germ vanishing or pole-of-order `-n`,
* `⊤` if `f` vanishes on a punctured neighborhood of `p` (in particular
  for the zero germ),
* `0` (junk) if `f` is not meromorphic at `p`.

Chart independence is `orderAt_eq_meromorphicOrderAt_of_mem_maximalAtlas`.
-/
noncomputable def orderAt (p : X) (f : X → ℂ) : WithTop ℤ :=
  meromorphicOrderAt (f ∘ (extChartAt 𝓘(ℂ) p).symm) (extChartAt 𝓘(ℂ) p p)

/-!
### Bridging `extChartAt` and `chartAt`

`extChartAt 𝓘(ℂ) p = (chartAt ℂ p).extend 𝓘(ℂ)`, which on the trivial
model `𝓘(ℂ) = id` coincides with `chartAt ℂ p` as a function. We
record the two pointwise identifications used in the chart-independence
proof.
-/

/--
The canonical extended chart at `p` agrees with `chartAt ℂ p` as a
function. Follows from `extChartAt_coe` and `modelWithCornersSelf_coe`.
-/
theorem extChartAt_eq_chartAt (p : X) :
    ⇑(extChartAt 𝓘(ℂ) p) = chartAt ℂ p := by
  funext x
  simp

/--
The canonical extended chart's inverse agrees with `(chartAt ℂ p).symm`
as a function.
-/
theorem extChartAt_symm_eq_chartAt_symm (p : X) :
    ⇑(extChartAt 𝓘(ℂ) p).symm = (chartAt ℂ p).symm := by
  funext x
  simp

/-- The `extChartAt`-form of `orderAt` rewrites in terms of `chartAt`. -/
theorem orderAt_eq_chartAt (p : X) (f : X → ℂ) :
    orderAt p f =
      meromorphicOrderAt (f ∘ (chartAt ℂ p).symm) (chartAt ℂ p p) := by
  unfold orderAt
  rw [extChartAt_symm_eq_chartAt_symm, extChartAt_eq_chartAt]

/-!
### Punctured-neighborhood agreement of two chart pullbacks

For any chart `e` at `p` (containing `p` in its source), the pullback
`f ∘ e.symm` agrees, on a neighborhood of `e p`, with the composition
`(f ∘ (chartAt ℂ p).symm) ∘ (chartAt ℂ p ∘ e.symm)`. This is the
bookkeeping needed to apply `meromorphicOrderAt_congr` and
`meromorphicOrderAt_comp_of_deriv_ne_zero` together.
-/

/--
On the open set where `e.symm` lands in `(chartAt ℂ p).source`,
`f ∘ e.symm` factors as `(f ∘ (chartAt ℂ p).symm) ∘ (chartAt ℂ p ∘ e.symm)`.
-/
theorem comp_eqOn
    {p : X} (e : OpenPartialHomeomorph X ℂ) (f : X → ℂ) :
    EqOn (f ∘ e.symm)
      ((f ∘ (chartAt ℂ p).symm) ∘ (chartAt ℂ p ∘ e.symm))
      (e.target ∩ e.symm ⁻¹' (chartAt ℂ p).source) := by
  intro y hy
  obtain ⟨_, hy₂⟩ := hy
  have h := (chartAt ℂ p).left_inv hy₂
  simp [Function.comp, h]

/--
The set `e.target ∩ e.symm ⁻¹' (chartAt ℂ p).source` is a neighborhood
of `e p` whenever `p` lies in `e.source`.
-/
theorem target_inter_preimage_mem_nhds
    {p : X} (e : OpenPartialHomeomorph X ℂ) (hp : p ∈ e.source) :
    e.target ∩ e.symm ⁻¹' (chartAt ℂ p).source ∈ 𝓝 (e p) := by
  refine Filter.inter_mem ?_ ?_
  · exact e.open_target.mem_nhds (e.map_source hp)
  · refine e.symm.continuousAt (e.map_source hp) ?_
    rw [e.left_inv hp]
    exact (chartAt ℂ p).open_source.mem_nhds (mem_chart_source ℂ p)

/--
**Punctured-neighborhood agreement.** The pullback `f ∘ e.symm`
agrees with the composite `(f ∘ (chartAt ℂ p).symm) ∘ (chartAt ℂ p ∘ e.symm)`
on a punctured neighborhood of `e p`.
-/
theorem eventuallyEq_pullback
    {p : X} (e : OpenPartialHomeomorph X ℂ) (hp : p ∈ e.source)
    (f : X → ℂ) :
    (f ∘ e.symm) =ᶠ[𝓝[≠] (e p)]
      (f ∘ (chartAt ℂ p).symm) ∘ (chartAt ℂ p ∘ e.symm) := by
  have hmem : e.target ∩ e.symm ⁻¹' (chartAt ℂ p).source ∈ 𝓝 (e p) :=
    target_inter_preimage_mem_nhds e hp
  filter_upwards [Filter.mem_inf_of_left hmem] with y hy
  exact comp_eqOn e f hy

/-!
### Chart-independence

Below this point we assume `IsManifold 𝓘(ℂ) ω X` (analytic complex
1-manifold). The chart-independence theorem reduces to two sub-obligations
about the transition map `g := chartAt ℂ p ∘ e.symm`:

* `transition_analyticAt` — the transition is analytic at `e p`.
* `transition_deriv_ne_zero` — the transition has nonzero derivative at `e p`.
-/

set_option linter.unusedSectionVars false

variable [IsManifold 𝓘(ℂ) ω X]

/--
**Generalized analyticity of transitions.** For any two charts
`e₁, e₂ ∈ maximalAtlas 𝓘(ℂ) ω X` containing `p` in their sources, the
transition `e₂ ∘ e₁.symm` is analytic at `e₁ p`.

Proof: `compatible_of_mem_maximalAtlas` gives
`e₁.symm.trans e₂ ∈ contDiffGroupoid ω 𝓘(ℂ)`. Unfolding through
`mem_groupoid_of_pregroupoid` and `contDiffPregroupoid` (and simplifying
under the trivial model `𝓘(ℂ)`) gives `ContDiffOn ℂ ω (e₂ ∘ e₁.symm)`
on the open transition source. Restricting to a neighborhood of `e₁ p`
upgrades to `ContDiffAt`, then `ContDiffAt.analyticAt` finishes.

Note: the proof depends on the maximal-atlas membership but not on the
`IsManifold` typeclass directly; we keep the typeclass in scope anyway
for uniformity with the rest of the section.
-/
theorem analyticAt_transition_of_mem_maximalAtlas
    {p : X} {e₁ e₂ : OpenPartialHomeomorph X ℂ}
    (he₁ : e₁ ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X)
    (he₂ : e₂ ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X)
    (hp₁ : p ∈ e₁.source) (hp₂ : p ∈ e₂.source) :
    AnalyticAt ℂ (e₂ ∘ e₁.symm) (e₁ p) := by
  -- Step 1: get groupoid membership of the transition.
  have hcompat := IsManifold.compatible_of_mem_maximalAtlas he₁ he₂
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at hcompat
  -- The forward (toFun) component of the pregroupoid property.
  have hcd := hcompat.1
  -- Step 2: simplify under the trivial model `𝓘(ℂ)`.
  -- `contDiffPregroupoid.property f s` is
  -- `ContDiffOn ℂ ω (𝓘(ℂ) ∘ f ∘ 𝓘(ℂ).symm) (𝓘(ℂ).symm ⁻¹' s ∩ range 𝓘(ℂ))`,
  -- which reduces to `ContDiffOn ℂ ω f s` since `𝓘(ℂ) = id` and
  -- `range 𝓘(ℂ) = univ`.
  simp only [contDiffPregroupoid, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id,
    range_id, preimage_id, inter_univ] at hcd
  -- Step 3: rewrite through `coe_trans` so the function becomes `e₂ ∘ e₁.symm`.
  have hcoe : ⇑(e₁.symm.trans e₂) = e₂ ∘ e₁.symm := by
    funext y; rfl
  rw [hcoe] at hcd
  -- Step 4: `e₁ p` is in the (open) transition source.
  have hep_target : e₁ p ∈ e₁.symm.source := by
    show e₁ p ∈ e₁.target
    exact e₁.map_source hp₁
  have hep_pre : e₁.symm (e₁ p) ∈ e₂.source := by
    rw [e₁.left_inv hp₁]; exact hp₂
  have hep_mem : e₁ p ∈ (e₁.symm.trans e₂).source := by
    rw [OpenPartialHomeomorph.trans_source]
    exact ⟨hep_target, hep_pre⟩
  -- Step 5: upgrade `ContDiffOn` at an interior point to `ContDiffAt`.
  have hopen : IsOpen (e₁.symm.trans e₂).source := (e₁.symm.trans e₂).open_source
  have hcdat : ContDiffAt ℂ ω (e₂ ∘ e₁.symm) (e₁ p) :=
    (hcd (e₁ p) hep_mem).contDiffAt (hopen.mem_nhds hep_mem)
  -- Step 6: `ContDiffAt 𝕜 ω → AnalyticAt 𝕜`.
  exact hcdat.analyticAt


theorem transition_analyticAt
    {p : X} (e : OpenPartialHomeomorph X ℂ)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X) (hp : p ∈ e.source) :
    AnalyticAt ℂ (chartAt ℂ p ∘ e.symm) (e p) :=
  analyticAt_transition_of_mem_maximalAtlas he
    (IsManifold.chart_mem_maximalAtlas p) hp (mem_chart_source ℂ p)

/--
Proof: the symmetric transition `e ∘ (chartAt ℂ p).symm` is also analytic
(apply the generalized lemma with chart roles swapped). The two compose
to the identity on a neighborhood of `e p`. Differentiating via the chain
rule gives `(deriv g')(g(e p)) * (deriv g)(e p) = 1`, so neither factor
can be zero.
-/
theorem transition_deriv_ne_zero
    {p : X} (e : OpenPartialHomeomorph X ℂ)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X) (hp : p ∈ e.source) :
    deriv (chartAt ℂ p ∘ e.symm) (e p) ≠ 0 := by
  -- The forward and backward transitions, both analytic.
  have hg : AnalyticAt ℂ (chartAt ℂ p ∘ e.symm) (e p) :=
    transition_analyticAt e he hp
  have hgep : (chartAt ℂ p ∘ e.symm) (e p) = chartAt ℂ p p := by
    simp [Function.comp_apply, e.left_inv hp]
  have hg' : AnalyticAt ℂ (e ∘ (chartAt ℂ p).symm) (chartAt ℂ p p) :=
    analyticAt_transition_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas p) he (mem_chart_source ℂ p) hp
  have hid : (e ∘ (chartAt ℂ p).symm) ∘ (chartAt ℂ p ∘ e.symm) =ᶠ[𝓝 (e p)] id := by
    have hmem : e.target ∩ e.symm ⁻¹' (chartAt ℂ p).source ∈ 𝓝 (e p) :=
      target_inter_preimage_mem_nhds e hp
    filter_upwards [hmem] with y hy
    obtain ⟨hy₁, hy₂⟩ := hy
    show e ((chartAt ℂ p).symm ((chartAt ℂ p) (e.symm y))) = y
    rw [(chartAt ℂ p).left_inv hy₂, e.right_inv hy₁]
  have hg_d : HasDerivAt (chartAt ℂ p ∘ e.symm)
      (deriv (chartAt ℂ p ∘ e.symm) (e p)) (e p) :=
    hg.differentiableAt.hasDerivAt
  have hg'_d : HasDerivAt (e ∘ (chartAt ℂ p).symm)
      (deriv (e ∘ (chartAt ℂ p).symm) (chartAt ℂ p p)) (chartAt ℂ p p) :=
    hg'.differentiableAt.hasDerivAt
  -- `comp_of_eq` consumes the equality `chartAt ℂ p p = (chartAt ℂ p ∘ e.symm) (e p)`,
  -- avoiding higher-order unification on the third HasDerivAt argument.
  -- Note: the lemma takes `x` (here `e p`) as an explicit positional argument,
  -- per the section variable convention in `Mathlib/Analysis/Calculus/Deriv/Comp.lean`.
  have hcomp : HasDerivAt ((e ∘ (chartAt ℂ p).symm) ∘ (chartAt ℂ p ∘ e.symm))
      (deriv (e ∘ (chartAt ℂ p).symm) (chartAt ℂ p p) *
        deriv (chartAt ℂ p ∘ e.symm) (e p)) (e p) :=
    HasDerivAt.comp_of_eq (e p) hg'_d hg_d hgep.symm
  have hcomp1 : HasDerivAt ((e ∘ (chartAt ℂ p).symm) ∘ (chartAt ℂ p ∘ e.symm))
      (1 : ℂ) (e p) :=
    (hasDerivAt_id (e p)).congr_of_eventuallyEq hid
  -- Uniqueness of the derivative.
  have hprod :
      deriv (e ∘ (chartAt ℂ p).symm) (chartAt ℂ p p) *
        deriv (chartAt ℂ p ∘ e.symm) (e p) = 1 :=
    hcomp.unique hcomp1
  -- Conclude.
  intro h
  rw [h, mul_zero] at hprod
  exact zero_ne_one hprod

/-! ### Main chart-independence theorem -/

/--
**Chart independence (canonical to arbitrary).** For any chart
`e ∈ maximalAtlas 𝓘(ℂ) ω X` with `p ∈ e.source`,
`orderAt p f = meromorphicOrderAt (f ∘ e.symm) (e p)`.

The proof composes:
1. `orderAt_eq_chartAt` rewrites the LHS through the canonical chart.
2. `eventuallyEq_pullback` and `meromorphicOrderAt_congr` rewrite
   `f ∘ e.symm` as the composite via the transition map.
3. `meromorphicOrderAt_comp_of_deriv_ne_zero`
   (`Mathlib.Analysis.Meromorphic.Order`, line 754), fed by
   `transition_analyticAt` and `transition_deriv_ne_zero`, evaluates the
   composite's order at the transition's image.
4. The transition sends `e p ↦ chartAt ℂ p p` (since `e.symm (e p) = p`),
   closing the chain.
-/
theorem orderAt_eq_meromorphicOrderAt_of_mem_maximalAtlas
    {p : X} (f : X → ℂ) (e : OpenPartialHomeomorph X ℂ)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X) (hp : p ∈ e.source) :
    orderAt p f = meromorphicOrderAt (f ∘ e.symm) (e p) := by
  -- Step 1: rewrite LHS through canonical chart.
  rw [orderAt_eq_chartAt]
  -- Step 2: rewrite `f ∘ e.symm` as the composite via the transition `g`.
  have hcongr : (f ∘ e.symm) =ᶠ[𝓝[≠] (e p)]
      (f ∘ (chartAt ℂ p).symm) ∘ (chartAt ℂ p ∘ e.symm) :=
    eventuallyEq_pullback e hp f
  rw [meromorphicOrderAt_congr hcongr]
  -- Step 3: apply `meromorphicOrderAt_comp_of_deriv_ne_zero` to the
  -- transition `g := chartAt ℂ p ∘ e.symm`.
  have hg_an : AnalyticAt ℂ (chartAt ℂ p ∘ e.symm) (e p) :=
    transition_analyticAt e he hp
  have hg_der : deriv (chartAt ℂ p ∘ e.symm) (e p) ≠ 0 :=
    transition_deriv_ne_zero e he hp
  rw [meromorphicOrderAt_comp_of_deriv_ne_zero hg_an hg_der]
  -- Step 4: identify `(chartAt ℂ p ∘ e.symm) (e p) = chartAt ℂ p p`.
  have hep : (chartAt ℂ p ∘ e.symm) (e p) = chartAt ℂ p p := by
    simp [Function.comp_apply, e.left_inv hp]
  rw [hep]

/-!
### Manifold meromorphy ⇒ chart-pullback meromorphy

If `f : X → ℂ` is meromorphic at every point of `X` (in the manifold sense
encoded by `MeromorphicAtX`), then for every base point `p : X`, the
chart pullback `f ∘ (chartAt ℂ p).symm` is meromorphic on the entire
chart target `(chartAt ℂ p).target`.

The proof at a point `w ∈ (chartAt ℂ p).target` factorises through the
chart at `q := (chartAt ℂ p).symm w`: the transition
`chartAt ℂ q ∘ (chartAt ℂ p).symm` is analytic at `w` with nonzero
derivative (the existing transition-analyticity infrastructure), so
`meromorphicAt_comp_iff_of_deriv_ne_zero` lifts manifold-level meromorphy
at `q` to chart-target-level meromorphy at `w`.
-/

/--
**Chart pullback is meromorphic at every target point.**

Given pointwise manifold meromorphy of `f`, the chart pullback through
`chartAt ℂ p` is `MeromorphicAt` at every `w ∈ (chartAt ℂ p).target`.
-/
theorem meromorphicAt_chart_pullback_of_meromorphicAtX
    {f : X → ℂ} (hf : ∀ q : X, MeromorphicAtX f q) (p : X)
    {w : ℂ} (hw : w ∈ (chartAt ℂ p).target) :
    MeromorphicAt (f ∘ (chartAt ℂ p).symm) w := by
  set q : X := (chartAt ℂ p).symm w with hq_def
  have hq_source : q ∈ (chartAt ℂ p).source := (chartAt ℂ p).map_target hw
  have hpq : (chartAt ℂ p) q = w := (chartAt ℂ p).right_inv hw
  -- Membership of charts in the maximal atlas.
  have hp_mem : (chartAt ℂ p) ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X :=
    IsManifold.chart_mem_maximalAtlas p
  have hq_mem : (chartAt ℂ q) ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X :=
    IsManifold.chart_mem_maximalAtlas q
  have hq_q_source : q ∈ (chartAt ℂ q).source := mem_chart_source ℂ q
  -- The transition `chartAt ℂ q ∘ (chartAt ℂ p).symm` is analytic at `w`.
  have h_an : AnalyticAt ℂ ((chartAt ℂ q) ∘ (chartAt ℂ p).symm) w := by
    rw [show w = (chartAt ℂ p) q from hpq.symm]
    exact analyticAt_transition_of_mem_maximalAtlas hp_mem hq_mem hq_source hq_q_source
  -- Its derivative at `w` is nonzero.
  have h_der : deriv ((chartAt ℂ q) ∘ (chartAt ℂ p).symm) w ≠ 0 := by
    rw [show w = (chartAt ℂ p) q from hpq.symm]
    exact transition_deriv_ne_zero (chartAt ℂ p) hp_mem hq_source
  -- Manifold meromorphy at `q` translates to `MeromorphicAt (f ∘ chartAt ℂ q .symm)`
  -- at `chartAt ℂ q q`.
  have hfq : MeromorphicAt (f ∘ (chartAt ℂ q).symm) ((chartAt ℂ q) q) := by
    have h := hf q
    unfold MeromorphicAtX at h
    rwa [extChartAt_symm_eq_chartAt_symm, extChartAt_eq_chartAt] at h
  -- Lift to meromorphy of the composite at `w`.
  have hcomp : MeromorphicAt
      ((f ∘ (chartAt ℂ q).symm) ∘ ((chartAt ℂ q) ∘ (chartAt ℂ p).symm)) w := by
    rw [meromorphicAt_comp_iff_of_deriv_ne_zero h_an h_der]
    have heval : ((chartAt ℂ q) ∘ (chartAt ℂ p).symm) w = (chartAt ℂ q) q := by
      simp [Function.comp_apply, hq_def]
    rw [heval]; exact hfq
  -- The composite agrees with `f ∘ (chartAt ℂ p).symm` on a punctured nbhd of `w`.
  -- Use `eventuallyEq_pullback` with role-bookkeeping (outer chart at `q`, `e := chartAt ℂ p`).
  have heq : (f ∘ (chartAt ℂ p).symm) =ᶠ[𝓝[≠] w]
      (f ∘ (chartAt ℂ q).symm) ∘ ((chartAt ℂ q) ∘ (chartAt ℂ p).symm) := by
    have := eventuallyEq_pullback (p := q) (chartAt ℂ p) hq_source f
    rwa [hpq] at this
  exact hcomp.congr heq.symm

/--
**Chart pullback is meromorphic on the chart target.**

Packages `meromorphicAt_chart_pullback_of_meromorphicAtX` as a
`MeromorphicOn` statement.
-/
theorem meromorphicOn_chart_pullback_of_meromorphicAtX
    {f : X → ℂ} (hf : ∀ q : X, MeromorphicAtX f q) (p : X) :
    MeromorphicOn (f ∘ (chartAt ℂ p).symm) (chartAt ℂ p).target :=
  fun _w hw ↦ meromorphicAt_chart_pullback_of_meromorphicAtX hf p hw

/--
**Chart-independence (two arbitrary atlas charts).** For two charts
`e₁, e₂ ∈ maximalAtlas 𝓘(ℂ) ω X` both containing `p` in their sources,
the meromorphic-order pullbacks agree.
-/
theorem meromorphicOrderAt_pullback_eq
    {p : X} (f : X → ℂ)
    {e₁ e₂ : OpenPartialHomeomorph X ℂ}
    (he₁ : e₁ ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X) (hp₁ : p ∈ e₁.source)
    (he₂ : e₂ ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X) (hp₂ : p ∈ e₂.source) :
    meromorphicOrderAt (f ∘ e₁.symm) (e₁ p) =
      meromorphicOrderAt (f ∘ e₂.symm) (e₂ p) := by
  rw [← orderAt_eq_meromorphicOrderAt_of_mem_maximalAtlas f e₁ he₁ hp₁,
      ← orderAt_eq_meromorphicOrderAt_of_mem_maximalAtlas f e₂ he₂ hp₂]

/-!
### Connectedness propagation of meromorphic non-vanishing

`isClopen_setOf_orderAt_eq_top` says the manifold-level set of points
where `f` is locally identically zero is clopen — a transfer of
Mathlib's `MeromorphicOn.isClopen_setOf_meromorphicOrderAt_eq_top`
through the chart-pullback machinery developed above. Combined with
`[PreconnectedSpace X]` (`orderAt_ne_top_of_exists`), it lifts the
"`f` is non-vanishing somewhere" hypothesis to "`f` is non-vanishing
everywhere", which is the analytic-identity-principle leg of the
classical "nonzero meromorphic function" definition on a connected
Riemann surface.
-/

/--
Helper for `isClopen_setOf_orderAt_eq_top`: extract the chart-target
ambient open set carrying a chart-target subtype-open property of
`meromorphicOrderAt (f ∘ chartAt ℂ p .symm)`, transport it to
`X` via `chartAt ℂ p`, and conclude the corresponding `orderAt`
property is open in `X`.

Encapsulates the boilerplate shared by both `IsOpen Z` and `IsOpen Zᶜ`
for `Z = {q | orderAt q f = ⊤}`.
-/
private theorem isOpen_setOf_orderAt_of_chartTarget_open
    {f : X → ℂ} (Q : WithTop ℤ → Prop)
    (hQ_chart : ∀ p : X, IsOpen
        {u : (chartAt ℂ p).target |
          Q (meromorphicOrderAt (f ∘ (chartAt ℂ p).symm) ↑u)}) :
    IsOpen {q : X | Q (orderAt q f)} := by
  rw [isOpen_iff_forall_mem_open]
  intro p hp
  set chart_p := chartAt ℂ p with hchart_p_def
  have hp_atlas : chart_p ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X :=
    IsManifold.chart_mem_maximalAtlas p
  have hp_source : p ∈ chart_p.source := mem_chart_source ℂ p
  have hp_target : chart_p p ∈ chart_p.target := chart_p.map_source hp_source
  have hQ_p := hQ_chart p
  rw [isOpen_induced_iff] at hQ_p
  obtain ⟨T, hT_open, hT_eq⟩ := hQ_p
  have h_chart_indep : ∀ {q : X}, q ∈ chart_p.source →
      orderAt q f = meromorphicOrderAt (f ∘ chart_p.symm) (chart_p q) :=
    fun {q} hq => orderAt_eq_meromorphicOrderAt_of_mem_maximalAtlas
      (p := q) f chart_p hp_atlas hq
  have h_p_in_T : chart_p p ∈ T := by
    have h_subtype : (⟨chart_p p, hp_target⟩ : chart_p.target) ∈
        ({u | Q (meromorphicOrderAt (f ∘ chart_p.symm) ↑u)} : Set chart_p.target) := by
      show Q (meromorphicOrderAt (f ∘ chart_p.symm) (chart_p p))
      rw [← h_chart_indep hp_source]
      exact hp
    rw [← hT_eq] at h_subtype
    exact h_subtype
  refine ⟨chart_p.source ∩ chart_p ⁻¹' T, ?_,
          chart_p.isOpen_inter_preimage hT_open, hp_source, h_p_in_T⟩
  rintro q ⟨hq_src, hq_T⟩
  show Q (orderAt q f)
  have hcq_target : chart_p q ∈ chart_p.target := chart_p.map_source hq_src
  have h_subtype : (⟨chart_p q, hcq_target⟩ : chart_p.target) ∈
      ({u | Q (meromorphicOrderAt (f ∘ chart_p.symm) ↑u)} : Set chart_p.target) := by
    rw [← hT_eq]; exact hq_T
  rw [h_chart_indep hq_src]
  exact h_subtype

/--
**The set of locally-identically-zero points is clopen.**

For `f : X → ℂ` meromorphic at every point of an analytic complex
1-manifold `X`, the set `{q : X | orderAt q f = ⊤}` is clopen.

Proof: Mathlib's `MeromorphicOn.isClopen_setOf_meromorphicOrderAt_eq_top`
gives the analogous fact for the chart pullback `f ∘ (chartAt ℂ p).symm`
on each `(chartAt ℂ p).target`; the chart-pullback meromorphy
(`meromorphicOn_chart_pullback_of_meromorphicAtX`) and chart-independence
(`orderAt_eq_meromorphicOrderAt_of_mem_maximalAtlas`) transport the
result to the manifold via the helper
`isOpen_setOf_orderAt_of_chartTarget_open` applied separately to the
`= ⊤` and `≠ ⊤` predicates.
-/
theorem isClopen_setOf_orderAt_eq_top
    {f : X → ℂ} (hf : ∀ q : X, MeromorphicAtX f q) :
    IsClopen {q : X | orderAt q f = ⊤} := by
  have hOpen_top : ∀ p : X, IsOpen
      {u : (chartAt ℂ p).target |
        meromorphicOrderAt (f ∘ (chartAt ℂ p).symm) ↑u = ⊤} := fun p =>
    (meromorphicOn_chart_pullback_of_meromorphicAtX hf p).isClopen_setOf_meromorphicOrderAt_eq_top.isOpen
  have hOpen_ne_top : ∀ p : X, IsOpen
      {u : (chartAt ℂ p).target |
        meromorphicOrderAt (f ∘ (chartAt ℂ p).symm) ↑u ≠ ⊤} := fun p =>
    isOpen_compl_iff.mpr
      (meromorphicOn_chart_pullback_of_meromorphicAtX hf p).isClopen_setOf_meromorphicOrderAt_eq_top.isClosed
  refine ⟨?_, isOpen_setOf_orderAt_of_chartTarget_open (· = ⊤) hOpen_top⟩
  exact isOpen_compl_iff.mp
    (isOpen_setOf_orderAt_of_chartTarget_open (· ≠ ⊤) hOpen_ne_top)

/--
**Identity-principle propagation of meromorphic non-vanishing.**

If `f` is meromorphic at every point of a preconnected complex
1-manifold `X` and has finite vanishing order at some single point,
then `f` has finite vanishing order at every point. The classical
"identity principle" leg of "nonzero meromorphic function on a
connected Riemann surface".
-/
theorem orderAt_ne_top_of_exists [PreconnectedSpace X]
    {f : X → ℂ} (hf : ∀ q : X, MeromorphicAtX f q)
    (h_nontriv : ∃ p : X, orderAt p f ≠ ⊤) :
    ∀ q : X, orderAt q f ≠ ⊤ := by
  intro q hq_top
  rcases isClopen_iff.mp (isClopen_setOf_orderAt_eq_top hf) with h_empty | h_univ
  · rw [Set.eq_empty_iff_forall_notMem] at h_empty
    exact h_empty q hq_top
  · obtain ⟨p₀, hp₀⟩ := h_nontriv
    apply hp₀
    have hp₀_in : p₀ ∈ ({q | orderAt q f = ⊤} : Set X) := h_univ ▸ Set.mem_univ p₀
    exact hp₀_in

end Jacobians.Vendor.Wallace.HolomorphicForms.VanishingOrder
