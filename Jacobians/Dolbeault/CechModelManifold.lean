/-
  Čech finiteness — the germ ↔ sup-norm comparison ("K-bridge"), manifold side.

  Part of discharging `exists_cechModel` (Forster 14.9); see `docs/cech_finiteness_research.md`.
  Companion to `CechModelBridge.lean` (the `BddHol` codomain side). Here: the chart-pullback of a
  holomorphic `𝒪`-section is `AnalyticOn` the chart-image — the analyticity hypothesis that
  `BddHol.ofAnalyticOn` consumes.

  The natural holomorphy datum is stated in each point's OWN chart (matching `ordU`/`OmegaD`), so we
  first build the missing **point-level** chart-change: `CechH0.analyticAt_chart_change` and
  `transition_analyticAt` only act at a chart's *centre*; we need analyticity transported to a fixed
  cover-chart `y` at an arbitrary point `x` of the overlap. `transition_analyticAt_of_mem` (the
  transition map analytic at any overlap point) and `analyticAt_chart_change_to` (own-chart →
  cover-chart `y`) provide that, then `analyticOn_pullback_of_holo` packages it.

  Sorry-free; reuses only the axiom-clean chart machinery (`contMDiffOn_chart`, `ContDiffAt.analyticAt`).
-/
import Jacobians.Dolbeault.CechH0
import Jacobians.Dolbeault.CechModelBridge

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)
open Filter

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **The chart transition `chartAt z ∘ (chartAt y).symm` is analytic at `chartAt y x`** for any
point `x` in the overlap of the two chart sources (generalizes `transition_analyticAt`, which is the
case `x = z` = chart centre). Chart and inverse-chart are `C^ω`, composition `C^ω`, `C^ω = analytic`. -/
theorem transition_analyticAt_of_mem {y z x : X}
    (hxy : x ∈ (chartAt (H := ℂ) y).source) (hxz : x ∈ (chartAt (H := ℂ) z).source) :
    AnalyticAt ℂ ((chartAt (H := ℂ) z) ∘ (chartAt (H := ℂ) y).symm) ((chartAt (H := ℂ) y) x) := by
  have hw_tgt : (chartAt (H := ℂ) y) x ∈ (chartAt (H := ℂ) y).target :=
    (chartAt (H := ℂ) y).map_source hxy
  have h1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt (H := ℂ) y).symm ((chartAt (H := ℂ) y) x) :=
    ((contMDiffOn_chart_symm (I := 𝓘(ℂ)) (n := ω) (x := y)) _ hw_tgt).contMDiffAt
      ((chartAt (H := ℂ) y).open_target.mem_nhds hw_tgt)
  have hey : (chartAt (H := ℂ) y).symm ((chartAt (H := ℂ) y) x) = x :=
    (chartAt (H := ℂ) y).left_inv hxy
  have h2 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt (H := ℂ) z)
      ((chartAt (H := ℂ) y).symm ((chartAt (H := ℂ) y) x)) := by
    rw [hey]
    exact ((contMDiffOn_chart (I := 𝓘(ℂ)) (n := ω) (x := z)) _ hxz).contMDiffAt
      ((chartAt (H := ℂ) z).open_source.mem_nhds hxz)
  exact (contMDiffAt_iff_contDiffAt.1
    (ContMDiffAt.comp (I' := 𝓘(ℂ)) ((chartAt (H := ℂ) y) x) h2 h1)).analyticAt

/-- **Own-chart → cover-chart analyticity.** If `h` read in its *own* chart at `x` is analytic, then
`h` read in the cover-chart `y` is analytic at `chartAt y x` (for `x` in that chart's source). The
reverse of `CechH0.analyticAt_chart_change`, at a general point. -/
theorem analyticAt_chart_change_to {h : X → ℂ} {y x : X}
    (hxy : x ∈ (chartAt (H := ℂ) y).source)
    (ha : AnalyticAt ℂ (h ∘ (chartAt (H := ℂ) x).symm) ((chartAt (H := ℂ) x) x)) :
    AnalyticAt ℂ (h ∘ (chartAt (H := ℂ) y).symm) ((chartAt (H := ℂ) y) x) := by
  have hxx : x ∈ (chartAt (H := ℂ) x).source := mem_chart_source ℂ x
  have hwy_tgt : (chartAt (H := ℂ) y) x ∈ (chartAt (H := ℂ) y).target :=
    (chartAt (H := ℂ) y).map_source hxy
  have hφ := transition_analyticAt_of_mem (y := y) (z := x) hxy hxx
  have hφ_pt : ((chartAt (H := ℂ) x) ∘ (chartAt (H := ℂ) y).symm) ((chartAt (H := ℂ) y) x)
      = (chartAt (H := ℂ) x) x := by
    simp only [Function.comp_apply, (chartAt (H := ℂ) y).left_inv hxy]
  have hcomp : AnalyticAt ℂ ((h ∘ (chartAt (H := ℂ) x).symm) ∘
      ((chartAt (H := ℂ) x) ∘ (chartAt (H := ℂ) y).symm)) ((chartAt (H := ℂ) y) x) :=
    AnalyticAt.comp (hφ_pt ▸ ha) hφ
  have hmem : ∀ᶠ w in 𝓝 ((chartAt (H := ℂ) y) x),
      (chartAt (H := ℂ) y).symm w ∈ (chartAt (H := ℂ) x).source := by
    have hcont : ContinuousAt (chartAt (H := ℂ) y).symm ((chartAt (H := ℂ) y) x) :=
      (chartAt (H := ℂ) y).continuousAt_symm hwy_tgt
    have hh : (chartAt (H := ℂ) y).symm ((chartAt (H := ℂ) y) x) ∈ (chartAt (H := ℂ) x).source := by
      rw [(chartAt (H := ℂ) y).left_inv hxy]; exact hxx
    exact hcont.preimage_mem_nhds ((chartAt (H := ℂ) x).open_source.mem_nhds hh)
  have heq : (h ∘ (chartAt (H := ℂ) y).symm) =ᶠ[𝓝 ((chartAt (H := ℂ) y) x)]
      ((h ∘ (chartAt (H := ℂ) x).symm) ∘ ((chartAt (H := ℂ) x) ∘ (chartAt (H := ℂ) y).symm)) := by
    filter_upwards [hmem] with w hw
    simp only [Function.comp_apply, (chartAt (H := ℂ) x).left_inv hw]
  rw [analyticAt_congr heq]; exact hcomp

/-- **The chart-pullback of a holomorphic section is `AnalyticOn` the chart-image.**  If `h` is
holomorphic on `V ⊆ (chartAt y).source` (analytic in each point's own chart), then `h ∘ (chartAt y).symm`
is analytic on `(chartAt y) '' V`.  This is the analyticity input to `BddHol.ofAnalyticOn`. -/
theorem analyticOn_pullback_of_holo {y : X} {V : Set X} (hV : V ⊆ (chartAt (H := ℂ) y).source)
    {h : X → ℂ} (hh : ∀ x ∈ V, AnalyticAt ℂ (h ∘ (chartAt (H := ℂ) x).symm) ((chartAt (H := ℂ) x) x)) :
    AnalyticOn ℂ (h ∘ (chartAt (H := ℂ) y).symm) ((chartAt (H := ℂ) y) '' V) := by
  rintro w ⟨x, hxV, rfl⟩
  exact (analyticAt_chart_change_to (hV hxV) (hh x hxV)).analyticWithinAt

/-- **The single-section K-bridge.**  A holomorphic `𝒪₀` section `h` on `V ⊆ (chartAt y).source`,
read through the cover-chart `y` and restricted to a relatively-compact open `U' ⋐ (chartAt y) '' V`,
is a `BddHol U'` element (analytic via `analyticOn_pullback_of_holo`, bounded via the
relatively-compact shrinking).  The value is the section's chart-pullback `h ∘ (chartAt y).symm`.
This is the per-overlap building block of the germ→`BddHol` cochain map (`exists_cechModel`). -/
noncomputable def holoSectionToBddHol {y : X} {V : Set X} (hV : V ⊆ (chartAt (H := ℂ) y).source)
    {h : X → ℂ} (hh : ∀ x ∈ V, AnalyticAt ℂ (h ∘ (chartAt (H := ℂ) x).symm) ((chartAt (H := ℂ) x) x))
    {U' : Set ℂ} (hsub : closure U' ⊆ (chartAt (H := ℂ) y) '' V) (hcpt : IsCompact (closure U')) :
    BddHol U' :=
  BddHol.ofAnalyticOnOfRelCompact (analyticOn_pullback_of_holo hV hh) hsub hcpt

@[simp] theorem holoSectionToBddHol_toFun_of_mem {y : X} {V : Set X}
    (hV : V ⊆ (chartAt (H := ℂ) y).source) {h : X → ℂ}
    (hh : ∀ x ∈ V, AnalyticAt ℂ (h ∘ (chartAt (H := ℂ) x).symm) ((chartAt (H := ℂ) x) x))
    {U' : Set ℂ} (hsub : closure U' ⊆ (chartAt (H := ℂ) y) '' V) (hcpt : IsCompact (closure U'))
    {z : ℂ} (hz : z ∈ U') :
    (holoSectionToBddHol hV hh hsub hcpt).toFun z = h ((chartAt (H := ℂ) y).symm z) :=
  BddHol.ofAnalyticOnOfRelCompact_toFun_of_mem _ _ _ hz

end Jacobians.Dolbeault
