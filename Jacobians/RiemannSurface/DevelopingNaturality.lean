/-
Developing-value naturality under pullback along a holomorphic map.

The developing value of a pulled-back holomorphic 1-form along a continuous
path `γ` in `X` equals the developing value of the original form along
`f ∘ γ` in `Y`, provided the two chart-local coefficient families satisfy
the cross-manifold pullback transformation law (`IsPullbackCoeffRel`, the
two-manifold analogue of `SatisfiesCotangentCocycle`).

This is the analytic engine ("chart-level chain rule" `∫_γ f^*ω = ∫_{f∘γ} ω`)
for period-map naturality. Consumed by the discharge of
`AX_pushforwardAmbient_preserves_lattice` (issue #30), where the relation
hypothesis is verified for `pullbackOneForm` through the Kirov bridge.

The proofs mirror the single-manifold chart-transition lemmas in
`DevelopingMap.lean` (`pathChartBallPrimitive_endpoint_sub_eq_on_preconnected_overlap`
and `..._on_path_segment`), with the chart transition `φ₂ ∘ φ₁⁻¹` replaced by
the chart read `φ₂ ∘ f ∘ φ₁⁻¹` of `f` and the cocycle law replaced by the
pullback relation.
-/
import Jacobians.RiemannSurface.DevelopingMap

namespace Jacobians.RiemannSurface

open scoped Manifold Topology
open scoped ContDiff

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]
variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y]
  [IsManifold 𝓘(ℂ) ω Y]

/-- **Cross-manifold pullback transformation law.** The coefficient family of
`formX` is, in every pair of charts `(x, y)` with compatible domains, the
coefficient of `formY` read through the chart representation
`φ_y ∘ f ∘ φ_x⁻¹` of `f` and multiplied by its complex derivative — i.e.
`formX = f^* formY` chart-locally. This is the exact two-manifold analogue of
`SatisfiesCotangentCocycle` (which is the case `f = id`). -/
def IsPullbackCoeffRel (f : X → Y) (formX : HolomorphicOneForm X)
    (formY : HolomorphicOneForm Y) : Prop :=
  ∀ (x : X) (y : Y), ∀ z ∈ (extChartAt 𝓘(ℂ) x).target,
    f ((extChartAt 𝓘(ℂ) x).symm z) ∈ (extChartAt 𝓘(ℂ) y).source →
    formX.coeff x z =
      formY.coeff y ((extChartAt 𝓘(ℂ) y) (f ((extChartAt 𝓘(ℂ) x).symm z))) *
        (fderiv ℂ ((extChartAt 𝓘(ℂ) y) ∘ f ∘ (extChartAt 𝓘(ℂ) x).symm) z 1)

/-- The chart read `φ_q ∘ f ∘ φ_p⁻¹` of a holomorphic map `f : X → Y` is
complex differentiable at points of its natural domain. Two-manifold analogue
of `chartTransition_differentiableAt`. -/
lemma mapChartRead_differentiableAt {f : X → Y}
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) {p : X} {q : Y} {z : ℂ}
    (hz : z ∈ (extChartAt 𝓘(ℂ) p).target)
    (hq : f ((extChartAt 𝓘(ℂ) p).symm z) ∈ (extChartAt 𝓘(ℂ) q).source) :
    DifferentiableAt ℂ
      ((extChartAt 𝓘(ℂ) q) ∘ f ∘ (extChartAt 𝓘(ℂ) p).symm) z := by
  have hsymm_mdiff_within : MDifferentiableWithinAt 𝓘(ℂ) 𝓘(ℂ)
      (extChartAt 𝓘(ℂ) p).symm (Set.range (𝓘(ℂ))) z :=
    mdifferentiableWithinAt_extChartAt_symm hz
  have hsymm_mdiff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ)
      (extChartAt 𝓘(ℂ) p).symm z := by
    have hrange : (Set.range (𝓘(ℂ) : ModelWithCorners ℂ ℂ ℂ)) = Set.univ :=
      ModelWithCorners.range_eq_univ _
    rw [← mdifferentiableWithinAt_univ, ← hrange]
    exact hsymm_mdiff_within
  have hf_mdiff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f
      ((extChartAt 𝓘(ℂ) p).symm z) :=
    hf.mdifferentiableAt (by decide)
  have hchart_mdiff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ)
      (extChartAt 𝓘(ℂ) q) (f ((extChartAt 𝓘(ℂ) p).symm z)) := by
    apply mdifferentiableAt_extChartAt
    rwa [← extChartAt_source (I := 𝓘(ℂ))]
  exact ((hchart_mdiff.comp ((extChartAt 𝓘(ℂ) p).symm z) hf_mdiff).comp z
    hsymm_mdiff).differentiableAt

private lemma pullbackChartBallOverlap_isOpen {f : X → Y} (hf : Continuous f)
    (B₁ : PathChartBall X) (B₂ : PathChartBall Y) : IsOpen
    ({z : ℂ | z ∈ Metric.ball B₁.c B₁.r ∧
      f ((extChartAt 𝓘(ℂ) B₁.p).symm z) ∈ (extChartAt 𝓘(ℂ) B₂.p).source ∧
        (extChartAt 𝓘(ℂ) B₂.p) (f ((extChartAt 𝓘(ℂ) B₁.p).symm z)) ∈
          Metric.ball B₂.c B₂.r}) := by
  classical
  rw [isOpen_iff_forall_mem_open]
  intro z hz
  rcases hz with ⟨hz_ball₁, hz_source₂, hz_ball₂⟩
  let V : Set Y := (extChartAt 𝓘(ℂ) B₂.p).source ∩
      (extChartAt 𝓘(ℂ) B₂.p) ⁻¹' Metric.ball B₂.c B₂.r
  have hV_open : IsOpen V := by
    simpa [V, extChartAt_source] using
      (isOpen_extChartAt_preimage (I := 𝓘(ℂ)) B₂.p Metric.isOpen_ball)
  have hz_target₁ : z ∈ (extChartAt 𝓘(ℂ) B₁.p).target :=
    B₁.ball_subset_target hz_ball₁
  have hzV : f ((extChartAt 𝓘(ℂ) B₁.p).symm z) ∈ V := ⟨hz_source₂, hz_ball₂⟩
  have hcont : ContinuousAt (fun w => f ((extChartAt 𝓘(ℂ) B₁.p).symm w)) z :=
    hf.continuousAt.comp (continuousAt_extChartAt_symm'' (I := 𝓘(ℂ)) hz_target₁)
  have hpre_nhds : (fun w => f ((extChartAt 𝓘(ℂ) B₁.p).symm w)) ⁻¹' V ∈ 𝓝 z :=
    hcont.preimage_mem_nhds (hV_open.mem_nhds hzV)
  obtain ⟨W, hW_sub, hW_open, hzW⟩ := mem_nhds_iff.mp hpre_nhds
  refine ⟨Metric.ball B₁.c B₁.r ∩ W, ?_, Metric.isOpen_ball.inter hW_open,
    ⟨hz_ball₁, hzW⟩⟩
  intro y hy
  rcases hy with ⟨hy_ball, hyW⟩
  have hyV : f ((extChartAt 𝓘(ℂ) B₁.p).symm y) ∈ V := hW_sub hyW
  exact ⟨hy_ball, hyV.1, hyV.2⟩

/-- On an open preconnected coordinate set `U` in an `X`-chart whose image
under the chart read of `f` lies in a `Y`-chart ball, the chosen primitive of
the pulled-back form and the pullback of the chosen primitive of the original
form differ by a constant; hence their endpoint differences agree. Mirror of
`pathChartBallPrimitive_endpoint_sub_eq_on_preconnected_overlap` with the
chart transition replaced by the chart read of `f`. -/
theorem pathChartBallPrimitive_pullback_endpoint_sub_eq_on_preconnected_overlap
    {f : X → Y} (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    {formX : HolomorphicOneForm X} {formY : HolomorphicOneForm Y}
    (hrel : IsPullbackCoeffRel f formX formY)
    (B₁ : PathChartBall X) (B₂ : PathChartBall Y) {U : Set ℂ}
    (hU_open : IsOpen U) (hU_preconnected : IsPreconnected U)
    (hU_ball₁ : U ⊆ Metric.ball B₁.c B₁.r)
    (hU_ball₂ : ∀ z ∈ U,
      f ((extChartAt 𝓘(ℂ) B₁.p).symm z) ∈ (extChartAt 𝓘(ℂ) B₂.p).source ∧
        (extChartAt 𝓘(ℂ) B₂.p) (f ((extChartAt 𝓘(ℂ) B₁.p).symm z)) ∈
          Metric.ball B₂.c B₂.r)
    {a b : ℂ} (ha : a ∈ U) (hb : b ∈ U) :
    pathChartBallPrimitive formX B₁ b - pathChartBallPrimitive formX B₁ a =
      pathChartBallPrimitive formY B₂
          ((extChartAt 𝓘(ℂ) B₂.p) (f ((extChartAt 𝓘(ℂ) B₁.p).symm b))) -
        pathChartBallPrimitive formY B₂
          ((extChartAt 𝓘(ℂ) B₂.p) (f ((extChartAt 𝓘(ℂ) B₁.p).symm a))) := by
  classical
  let T : ℂ → ℂ := (extChartAt 𝓘(ℂ) B₂.p) ∘ f ∘ (extChartAt 𝓘(ℂ) B₁.p).symm
  let F₁ : ℂ → ℂ := pathChartBallPrimitive formX B₁
  let F₂ : ℂ → ℂ := fun z => pathChartBallPrimitive formY B₂ (T z)
  have hdiff₁ : DifferentiableOn ℂ F₁ U := by
    intro z hz
    exact ((pathChartBallPrimitive_hasDerivAt formX B₁) z
      (hU_ball₁ hz)).differentiableAt.differentiableWithinAt
  have hdiff₂ : DifferentiableOn ℂ F₂ U := by
    intro z hz
    let d : ℂ := fderiv ℂ T z 1
    have hz_target : z ∈ (extChartAt 𝓘(ℂ) B₁.p).target :=
      B₁.ball_subset_target (hU_ball₁ hz)
    have hTdiff : DifferentiableAt ℂ T z :=
      mapChartRead_differentiableAt hf hz_target (hU_ball₂ z hz).1
    have hTderiv : HasDerivAt T d z := by
      simpa [d] using hTdiff.hasDerivAt
    have hprim₂ : HasDerivAt (pathChartBallPrimitive formY B₂)
        (formY.coeff B₂.p (T z)) (T z) := by
      simpa [T] using
        (pathChartBallPrimitive_hasDerivAt formY B₂)
          ((extChartAt 𝓘(ℂ) B₂.p) (f ((extChartAt 𝓘(ℂ) B₁.p).symm z)))
          (hU_ball₂ z hz).2
    exact (hprim₂.comp z hTderiv).differentiableAt.differentiableWithinAt
  have hderiv_eq : U.EqOn (deriv F₁) (deriv F₂) := by
    intro z hz
    let d : ℂ := fderiv ℂ T z 1
    have hz_target : z ∈ (extChartAt 𝓘(ℂ) B₁.p).target :=
      B₁.ball_subset_target (hU_ball₁ hz)
    have hTdiff : DifferentiableAt ℂ T z :=
      mapChartRead_differentiableAt hf hz_target (hU_ball₂ z hz).1
    have hTderiv : HasDerivAt T d z := by
      simpa [d] using hTdiff.hasDerivAt
    have hprim₁ : HasDerivAt F₁ (formX.coeff B₁.p z) z := by
      simpa [F₁] using (pathChartBallPrimitive_hasDerivAt formX B₁) z (hU_ball₁ hz)
    have hprim₂ : HasDerivAt (pathChartBallPrimitive formY B₂)
        (formY.coeff B₂.p (T z)) (T z) := by
      simpa [T] using
        (pathChartBallPrimitive_hasDerivAt formY B₂)
          ((extChartAt 𝓘(ℂ) B₂.p) (f ((extChartAt 𝓘(ℂ) B₁.p).symm z)))
          (hU_ball₂ z hz).2
    have hcomp : HasDerivAt F₂ (formY.coeff B₂.p (T z) * d) z := by
      simpa [F₂] using hprim₂.comp z hTderiv
    have hpull : formX.coeff B₁.p z = formY.coeff B₂.p (T z) * d := by
      have hc := hrel B₁.p B₂.p z hz_target (hU_ball₂ z hz).1
      simpa [T, d, Function.comp_def] using hc
    calc
      deriv F₁ z = formX.coeff B₁.p z := hprim₁.deriv
      _ = formY.coeff B₂.p (T z) * d := hpull
      _ = deriv F₂ z := hcomp.deriv.symm
  obtain ⟨C, hC⟩ :=
    hU_open.exists_eq_add_of_deriv_eq hU_preconnected hdiff₁ hdiff₂ hderiv_eq
  have hCa := hC ha
  have hCb := hC hb
  calc
    pathChartBallPrimitive formX B₁ b - pathChartBallPrimitive formX B₁ a =
        F₁ b - F₁ a := rfl
    _ = (F₂ b + C) - (F₂ a + C) := by rw [hCb, hCa]
    _ = F₂ b - F₂ a := by abel
    _ = pathChartBallPrimitive formY B₂
            ((extChartAt 𝓘(ℂ) B₂.p) (f ((extChartAt 𝓘(ℂ) B₁.p).symm b))) -
          pathChartBallPrimitive formY B₂
            ((extChartAt 𝓘(ℂ) B₂.p) (f ((extChartAt 𝓘(ℂ) B₁.p).symm a))) := rfl

/-- Endpoint-difference equality across `f` on a path segment lying in an
`X`-chart-ball set for `γ` and in a `Y`-chart-ball set for `κ = f ∘ γ`.
Mirror of `pathChartBallPrimitive_endpoint_sub_eq_on_path_segment`. -/
lemma pathChartBallPrimitive_pullback_endpoint_sub_eq_on_path_segment
    {f : X → Y} (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    {formX : HolomorphicOneForm X} {formY : HolomorphicOneForm Y}
    (hrel : IsPullbackCoeffRel f formX formY)
    (γ : C(unitInterval, X)) (κ : C(unitInterval, Y))
    (hκ : ∀ w : unitInterval, κ w = f (γ w))
    (B₁ : PathChartBall X) (B₂ : PathChartBall Y) {u v : unitInterval}
    (huv : u ≤ v)
    (hseg₁ : Set.Icc u v ⊆ pathChartBallSet γ B₁)
    (hseg₂ : Set.Icc u v ⊆ pathChartBallSet κ B₂) :
    pathChartBallPrimitive formX B₁ ((extChartAt 𝓘(ℂ) B₁.p) (γ v)) -
        pathChartBallPrimitive formX B₁ ((extChartAt 𝓘(ℂ) B₁.p) (γ u)) =
      pathChartBallPrimitive formY B₂ ((extChartAt 𝓘(ℂ) B₂.p) (κ v)) -
        pathChartBallPrimitive formY B₂ ((extChartAt 𝓘(ℂ) B₂.p) (κ u)) := by
  classical
  let O : Set ℂ := {z : ℂ | z ∈ Metric.ball B₁.c B₁.r ∧
      f ((extChartAt 𝓘(ℂ) B₁.p).symm z) ∈ (extChartAt 𝓘(ℂ) B₂.p).source ∧
        (extChartAt 𝓘(ℂ) B₂.p) (f ((extChartAt 𝓘(ℂ) B₁.p).symm z)) ∈
          Metric.ball B₂.c B₂.r}
  let z : unitInterval → ℂ := fun w => (extChartAt 𝓘(ℂ) B₁.p) (γ w)
  have huI : u ∈ Set.Icc u v := ⟨le_rfl, huv⟩
  have hvI : v ∈ Set.Icc u v := ⟨huv, le_rfl⟩
  have hsource₁ : ∀ w ∈ Set.Icc u v, γ w ∈ (extChartAt 𝓘(ℂ) B₁.p).source := by
    intro w hw
    simpa [extChartAt_source] using (hseg₁ hw).1
  have hcont_z : ContinuousOn z (Set.Icc u v) := by
    simpa [z] using
      (continuousOn_extChartAt (I := 𝓘(ℂ)) B₁.p).comp γ.continuous.continuousOn
        hsource₁
  have hpre_image : IsPreconnected (z '' Set.Icc u v) :=
    isPreconnected_Icc.image z hcont_z
  have himage_sub_O : z '' Set.Icc u v ⊆ O := by
    intro y hy
    rcases hy with ⟨w, hw, rfl⟩
    have hw₁ := hseg₁ hw
    have hw₂ := hseg₂ hw
    have hw_source₁ : γ w ∈ (extChartAt 𝓘(ℂ) B₁.p).source := hsource₁ w hw
    have hsymm :
        (extChartAt 𝓘(ℂ) B₁.p).symm ((extChartAt 𝓘(ℂ) B₁.p) (γ w)) = γ w :=
      (extChartAt 𝓘(ℂ) B₁.p).left_inv hw_source₁
    refine ⟨hw₁.2, ?_, ?_⟩
    · rw [hsymm, ← hκ w]
      simpa [extChartAt_source] using hw₂.1
    · rw [hsymm, ← hκ w]
      exact hw₂.2
  let U : Set ℂ := connectedComponentIn O (z u)
  have hzuO : z u ∈ O := himage_sub_O ⟨u, huI, rfl⟩
  have hzvU : z v ∈ U := by
    have hsub := hpre_image.subset_connectedComponentIn (x := z u) ⟨u, huI, rfl⟩
      himage_sub_O
    exact hsub ⟨v, hvI, rfl⟩
  have hU_open : IsOpen U :=
    (pullbackChartBallOverlap_isOpen (X := X) (Y := Y) hf.continuous B₁
      B₂).connectedComponentIn
  have hU_pre : IsPreconnected U := by
    simpa [U] using (isPreconnected_connectedComponentIn (x := z u) (F := O))
  have hU_ball₁ : U ⊆ Metric.ball B₁.c B₁.r := by
    intro y hy
    exact (connectedComponentIn_subset O (z u) hy).1
  have hU_ball₂ : ∀ y ∈ U,
      f ((extChartAt 𝓘(ℂ) B₁.p).symm y) ∈ (extChartAt 𝓘(ℂ) B₂.p).source ∧
        (extChartAt 𝓘(ℂ) B₂.p) (f ((extChartAt 𝓘(ℂ) B₁.p).symm y)) ∈
          Metric.ball B₂.c B₂.r := by
    intro y hy
    exact (connectedComponentIn_subset O (z u) hy).2
  have hzuU : z u ∈ U := mem_connectedComponentIn hzuO
  have hbase :=
    pathChartBallPrimitive_pullback_endpoint_sub_eq_on_preconnected_overlap
      hf hrel B₁ B₂ hU_open hU_pre hU_ball₁ hU_ball₂ hzuU hzvU
  have hu_symm :
      (extChartAt 𝓘(ℂ) B₁.p).symm (z u) = γ u :=
    (extChartAt 𝓘(ℂ) B₁.p).left_inv (hsource₁ u huI)
  have hv_symm :
      (extChartAt 𝓘(ℂ) B₁.p).symm (z v) = γ v :=
    (extChartAt 𝓘(ℂ) B₁.p).left_inv (hsource₁ v hvI)
  rw [hu_symm, hv_symm, ← hκ u, ← hκ v] at hbase
  exact hbase

/-- **Developing-value naturality.** For `f : X → Y` holomorphic and forms
related by the pullback transformation law, the developing value of the
pulled-back form along any continuous path `γ` equals the developing value of
the original form along `f ∘ γ`. (Both basepoint arguments are definitionally
ignored by `developingValue`.) -/
theorem developingValue_comp_of_isPullbackCoeffRel
    {f : X → Y} (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    {formX : HolomorphicOneForm X} {formY : HolomorphicOneForm Y}
    (hrel : IsPullbackCoeffRel f formX formY)
    (x₀ : X) (y₀ : Y) (γ : C(unitInterval, X)) :
    developingValue x₀ formX γ =
      developingValue y₀ formY
        ((⟨f, hf.continuous⟩ : C(X, Y)).comp γ) := by
  classical
  set κ : C(unitInterval, Y) := (⟨f, hf.continuous⟩ : C(X, Y)).comp γ with hκ_def
  have hκ : ∀ w : unitInterval, κ w = f (γ w) := fun w => rfl
  -- A common subdivision: each cell lies in an `X`-chart-ball set for `γ`
  -- and a `Y`-chart-ball set for `κ` simultaneously (Lebesgue number on the
  -- product-indexed joint open cover).
  have hopen : ∀ P : PathChartBall X × PathChartBall Y,
      IsOpen (pathChartBallSet γ P.1 ∩ pathChartBallSet κ P.2) := fun P =>
    (isOpen_pathChartBallSet γ P.1).inter (isOpen_pathChartBallSet κ P.2)
  have hcover : Set.univ ⊆ ⋃ P : PathChartBall X × PathChartBall Y,
      pathChartBallSet γ P.1 ∩ pathChartBallSet κ P.2 := by
    intro w hw
    obtain ⟨B₁, hB₁⟩ := Set.mem_iUnion.mp (pathChartBallSet_cover γ hw)
    obtain ⟨B₂, hB₂⟩ := Set.mem_iUnion.mp (pathChartBallSet_cover κ hw)
    exact Set.mem_iUnion.2 ⟨(B₁, B₂), hB₁, hB₂⟩
  obtain ⟨t, ht_zero, ht_mono, ⟨k, ht_one⟩, ht_sub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hopen hcover
  let N : ℕ := k + 1
  let P : Fin N → PathChartBall X × PathChartBall Y :=
    fun i => Classical.choose (ht_sub i.val)
  have hP : ∀ i : Fin N, Set.Icc (t i.val) (t (i.val + 1)) ⊆
      pathChartBallSet γ (P i).1 ∩ pathChartBallSet κ (P i).2 := fun i =>
    Classical.choose_spec (ht_sub i.val)
  have hcell : ∀ i : Fin N, ∀ u ∈ Set.Icc
      ((fun j : Fin (N + 1) => t j.val) i.castSucc)
      ((fun j : Fin (N + 1) => t j.val) i.succ),
      u ∈ Set.Icc (t i.val) (t (i.val + 1)) := by
    intro i u hu
    constructor
    · simpa [Fin.val_castSucc] using hu.1
    · simpa [Fin.val_succ] using hu.2
  let S : PathChartBallSubdivision γ :=
    { n := N
      t := fun i : Fin (N + 1) => t i.val
      cellBall := fun i => (P i).1
      zero_eq := by simpa using ht_zero
      one_eq := by
        have hlast : t N = 1 := ht_one N (Nat.le_succ k)
        simpa [N, Fin.val_last] using hlast
      monotone_t := fun i j hij => ht_mono (Fin.val_le_of_le hij)
      cell_subset := fun i u hu => ((hP i) (hcell i u hu)).1 }
  let S' : PathChartBallSubdivision κ :=
    { n := N
      t := fun i : Fin (N + 1) => t i.val
      cellBall := fun i => (P i).2
      zero_eq := by simpa using ht_zero
      one_eq := by
        have hlast : t N = 1 := ht_one N (Nat.le_succ k)
        simpa [N, Fin.val_last] using hlast
      monotone_t := fun i j hij => ht_mono (Fin.val_le_of_le hij)
      cell_subset := fun i u hu => ((hP i) (hcell i u hu)).2 }
  rw [developingValue_eq_developingValueOfSubdivision x₀ formX γ S,
    developingValue_eq_developingValueOfSubdivision y₀ formY κ S']
  unfold developingValueOfSubdivision
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have huv : S.t i.castSucc ≤ S.t i.succ :=
    S.monotone_t (Fin.castSucc_le_succ i)
  have hseg₁ : Set.Icc (S.t i.castSucc) (S.t i.succ) ⊆
      pathChartBallSet γ (P i).1 := S.cell_subset i
  have hseg₂ : Set.Icc (S.t i.castSucc) (S.t i.succ) ⊆
      pathChartBallSet κ (P i).2 := S'.cell_subset i
  have hkey :=
    pathChartBallPrimitive_pullback_endpoint_sub_eq_on_path_segment
      hf hrel γ κ hκ (P i).1 (P i).2 huv hseg₁ hseg₂
  change pathChartBallPrimitive formX (P i).1
        ((extChartAt 𝓘(ℂ) (P i).1.p) (γ (S.t i.succ))) -
      pathChartBallPrimitive formX (P i).1
        ((extChartAt 𝓘(ℂ) (P i).1.p) (γ (S.t i.castSucc))) =
    pathChartBallPrimitive formY (P i).2
        ((extChartAt 𝓘(ℂ) (P i).2.p) (κ (S'.t i.succ))) -
      pathChartBallPrimitive formY (P i).2
        ((extChartAt 𝓘(ℂ) (P i).2.p) (κ (S'.t i.castSucc)))
  exact hkey

end Jacobians.RiemannSurface
