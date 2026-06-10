import Jacobians.Montel.Compactness
import Mathlib.Topology.VectorBundle.Basic

/-!
# Montel path — chart-transition estimate

The **chart-transition estimate** lifts per-chart inner-shrunkChart
precompactness (from `Jacobians/Montel/Compactness.lean` B.8) to
supNormK precompactness:

  `supNormK α ≤ M · sup_{x₀ ∈ chartCover} ‖localRepOnInnerShrunk α x₀‖_bcf`

where `M > 0` is a universal constant depending only on `X`'s chart
structure (not on α). This closes the final structural gap in Montel's
`exists_convergent_subseq_of_bounded` / `closedBall_isCompact`.

## Proof outline

For y ∈ chart source x₀ ∩ chart source x₀', the two chart-tangent-basis
vectors `e_{x₀}.symmL y 1` and `e_{x₀'}.symmL y 1` are both nonzero in
the 1-dim `T_y X`, hence proportional:
  `e_{x₀'}.symmL y 1 = c(y) · e_{x₀}.symmL y 1`
with `c(y) ≠ 0`. By ℂ-linearity of `α.toFun y`:
  `localRep α x₀' y = c(y) · localRep α x₀ y`
and hence `|localRep α x₀ y| = |localRep α x₀' y| / |c(y)|`.

The factor `c(y) = (coordChangeL ℂ e_{x₀'} e_{x₀} y) 1` is continuous
and nonzero on the overlap. On any compact subset of the overlap,
`1/|c(y)|` is bounded. Applying this at y ∈ shrunkChart x₀ ∩
innerShrunkChart x₀' (with x₀' chosen so y lies in the inner cover)
yields the estimate. Taking max over `chartCover × chartCover`
(finite) gives the uniform `M`.
-/

namespace Jacobians.Montel

open scoped Manifold ContDiff Topology
open Bundle Filter

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### The transition factor -/

/-- The chart-transition factor between two tangent-bundle trivializations,
evaluated at a point `y`. Equals `1` by convention if `y` is not in both
base sets. -/
noncomputable def chartTransitionFactor (x₀ x₀' y : X) : ℂ :=
  Trivialization.coordChangeL ℂ
    (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀')
    (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀) y 1

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X] in
/-- The chart-transition factor is nonzero (a CLE sends nonzero to nonzero). -/
theorem chartTransitionFactor_ne_zero (x₀ x₀' y : X) :
    chartTransitionFactor (X := X) x₀ x₀' y ≠ 0 := by
  unfold chartTransitionFactor
  intro hzero
  have : (1 : ℂ) = 0 := by
    have hinj := (Trivialization.coordChangeL ℂ
        (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀')
        (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀) y).injective
    apply hinj
    rw [hzero, ContinuousLinearEquiv.map_zero]
  exact one_ne_zero this

/-! ### Chart-transition relation for localRep -/

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X] in
/-- Key identity: `e.symmL y (c(y)) = e'.symmL y 1`, where
`c(y) = chartTransitionFactor x₀ x₀' y`, for y in both base sets. -/
theorem symmL_apply_chartTransitionFactor (x₀ x₀' y : X)
    (hy₀' : y ∈ (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀').baseSet)
    (hy₀ : y ∈ (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).baseSet) :
    (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).symmL ℂ y
      (chartTransitionFactor (X := X) x₀ x₀' y) =
      (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀').symmL ℂ y 1 := by
  set e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀
  set e' := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀'
  -- c(y) = (e ⟨y, e'.symm y 1⟩).2 = (e.linearEquivAt ℂ y hy₀) (e'.symm y 1).
  -- Apply e.symm on both sides: e.symm y (c(y)) = e'.symm y 1 (by inverse property).
  change e.symm y (chartTransitionFactor (X := X) x₀ x₀' y) = e'.symm y 1
  -- e.symm y c = (e.linearEquivAt ℂ y hy₀).symm c (by linearEquivAt_symm_apply).
  have h1 : e.symm y (chartTransitionFactor (X := X) x₀ x₀' y) =
      (e.linearEquivAt ℂ y hy₀).symm (chartTransitionFactor (X := X) x₀ x₀' y) := by
    rw [Trivialization.linearEquivAt_symm_apply]
  rw [h1]
  -- c = (e.linearEquivAt ℂ y hy₀) (e'.symm y 1) (from coordChangeL + linearEquivAt_apply).
  have h2 : chartTransitionFactor (X := X) x₀ x₀' y =
      (e.linearEquivAt ℂ y hy₀) (e'.symm y 1) := by
    unfold chartTransitionFactor
    rw [e'.coordChangeL_apply e ⟨hy₀', hy₀⟩ 1]
    rw [Trivialization.linearEquivAt_apply]
  rw [h2]
  -- (linEq).symm ∘ (linEq) = id on E y.
  exact (e.linearEquivAt ℂ y hy₀).left_inv (e'.symm y 1)

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X] in
/-- Chart-transition relation for `localRep`:
`localRep α x₀' y = c(y) · localRep α x₀ y` with `c = chartTransitionFactor`. -/
theorem localRep_chart_transition
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (x₀ x₀' y : X)
    (hy₀' : y ∈ (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀').baseSet)
    (hy₀ : y ∈ (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).baseSet) :
    localRep α x₀' y = chartTransitionFactor (X := X) x₀ x₀' y * localRep α x₀ y := by
  unfold localRep
  rw [← symmL_apply_chartTransitionFactor x₀ x₀' y hy₀' hy₀]
  -- Goal: α.toFun y (e.symmL y c) = c * α.toFun y (e.symmL y 1).
  set e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀
  set c := chartTransitionFactor (X := X) x₀ x₀' y with hc_def
  -- e.symmL y c = c • e.symmL y 1 (by ℂ-linearity + c = c·1 in ℂ).
  have h : e.symmL ℂ y c = c • e.symmL ℂ y 1 := by
    have : (c : ℂ) = c • (1 : ℂ) := by rw [smul_eq_mul, mul_one]
    conv_lhs => rw [this]
    exact map_smul (e.symmL ℂ y) c 1
  rw [h, map_smul, smul_eq_mul]

/-! ### Continuity of the chart-transition factor -/

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X] in
/-- Continuity of `chartTransitionFactor` on the overlap of two base sets. -/
theorem continuousOn_chartTransitionFactor (x₀ x₀' : X) :
    ContinuousOn (chartTransitionFactor (X := X) x₀ x₀')
      ((trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀').baseSet ∩
        (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).baseSet) := by
  unfold chartTransitionFactor
  -- continuousOn_coordChange gives continuity of y ↦ coordChangeL ℂ e' e y as a CLM
  have h := continuousOn_coordChange ℂ
      (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀')
      (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀)
  -- Apply at 1: composing with (evaluation at 1) preserves continuity.
  exact (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).continuous.comp_continuousOn h

/-! ### Pairwise chart-transition bound -/

omit [ConnectedSpace X] [Nonempty X] in
/-- **Pairwise bound**: for each chart pair `(x₀, x₀') ∈ chartCover²`, there's
a universal constant `M ≥ 0` such that for any α and any point y in the
overlap `shrunkChart x₀ ∩ innerShrunkChart x₀'`,
`‖localRep α x₀ y‖ ≤ M · ‖localRep α x₀' y‖`.

Proof: `1/‖chartTransitionFactor x₀ x₀' y‖` is continuous and bounded on
the compact overlap (since `c ≠ 0` there); take the sup as M. -/
theorem exists_pairwise_chart_transition_bound
    (x₀ x₀' : X) (hx₀ : x₀ ∈ (chartCover : Finset X))
    (hx₀' : x₀' ∈ (chartCover : Finset X)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
      (y : X), y ∈ shrunkChart (X := X) x₀ → y ∈ innerShrunkChart (X := X) x₀' →
        ‖localRep α x₀ y‖ ≤ M * ‖localRep α x₀' y‖ := by
  set K := shrunkChart (X := X) x₀ ∩ innerShrunkChart (X := X) x₀' with hK_def
  have hKcpt : IsCompact K :=
    (shrunkChart_isCompact x₀).inter_right (innerShrunkChart_isClosed x₀')
  -- K sits inside both base sets
  have hKbase_x₀' : K ⊆ (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀').baseSet := by
    intro y hy
    exact innerShrunkChart_subset_baseSet x₀' hx₀' hy.2
  have hKbase_x₀ : K ⊆ (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).baseSet := by
    intro y hy
    exact shrunkChart_subset_baseSet x₀ hx₀ hy.1
  have hKbase : K ⊆ (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀').baseSet ∩
      (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).baseSet := by
    intro y hy; exact ⟨hKbase_x₀' hy, hKbase_x₀ hy⟩
  -- g(y) := 1 / ‖c(y)‖ is continuous on K (c is cont, nonzero on overlap ⊇ K).
  have hg_cont : ContinuousOn (fun y => 1 / ‖chartTransitionFactor (X := X) x₀ x₀' y‖) K := by
    apply ContinuousOn.div₀ continuousOn_const
    · exact ((continuousOn_chartTransitionFactor x₀ x₀').mono hKbase).norm
    · intro y _
      exact norm_ne_zero_iff.mpr (chartTransitionFactor_ne_zero x₀ x₀' y)
  -- Bounded above on K
  have hbdd : BddAbove ((fun y => 1 / ‖chartTransitionFactor (X := X) x₀ x₀' y‖) '' K) :=
    hKcpt.bddAbove_image hg_cont
  obtain ⟨M, hMub⟩ := hbdd
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro α y hy_shrunk hy_inner
  have hy_K : y ∈ K := ⟨hy_shrunk, hy_inner⟩
  have hy_base_x₀' : y ∈ (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀').baseSet :=
    hKbase_x₀' hy_K
  have hy_base_x₀ : y ∈ (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).baseSet :=
    hKbase_x₀ hy_K
  -- localRep α x₀' y = c(y) * localRep α x₀ y.
  have hrel := localRep_chart_transition α x₀ x₀' y hy_base_x₀' hy_base_x₀
  -- So localRep α x₀ y = localRep α x₀' y / c(y). |localRep α x₀ y| ≤ (1/|c|) · |localRep α x₀' y|.
  have hc_ne : chartTransitionFactor (X := X) x₀ x₀' y ≠ 0 :=
    chartTransitionFactor_ne_zero x₀ x₀' y
  have hrel' : localRep α x₀ y =
      localRep α x₀' y / chartTransitionFactor (X := X) x₀ x₀' y := by
    rw [eq_div_iff hc_ne, mul_comm]
    exact hrel.symm
  rw [hrel', norm_div]
  have hg_y : (1 : ℝ) / ‖chartTransitionFactor (X := X) x₀ x₀' y‖ ≤ M :=
    hMub ⟨y, hy_K, rfl⟩
  have hg_y' : (1 : ℝ) / ‖chartTransitionFactor (X := X) x₀ x₀' y‖ ≤ max M 0 :=
    le_trans hg_y (le_max_left _ _)
  have hnorm_pos : 0 < ‖chartTransitionFactor (X := X) x₀ x₀' y‖ :=
    norm_pos_iff.mpr hc_ne
  rw [div_eq_inv_mul]
  calc ‖chartTransitionFactor (X := X) x₀ x₀' y‖⁻¹ * ‖localRep α x₀' y‖
      = (1 / ‖chartTransitionFactor (X := X) x₀ x₀' y‖) * ‖localRep α x₀' y‖ := by
        rw [one_div]
    _ ≤ max M 0 * ‖localRep α x₀' y‖ := by
        apply mul_le_mul_of_nonneg_right hg_y' (norm_nonneg _)

/-! ### Global chart-transition bound (aggregated over chartCover × chartCover)

For each pair `(x₀, x₀') ∈ chartCover²`, the pairwise bound yields an
`M_{x₀,x₀'} ≥ 0`. Taking max over the finite product gives a universal
`M` such that, for any α, for any y ∈ shrunkChart x₀ (x₀ ∈ chartCover),
there's x₀' ∈ chartCover with `y ∈ innerShrunkChart x₀'` (inner cover)
and `‖localRep α x₀ y‖ ≤ M · ‖localRep α x₀' y‖`.

Since `‖localRep α x₀' y‖ ≤ chartNormK (via inner shrinkage)` bounds the
right-hand side by the max inner chart-norm, we obtain
`supNormK α ≤ M · (max over chartCover of inner-chart-norm)`. -/

omit [ConnectedSpace X] in
/-- **Global chart-transition bound** (pointwise form).
There is a universal constant `M ≥ 0` such that for any α, for any
`x₀ ∈ chartCover` and any `y ∈ shrunkChart x₀`, there exists
`x₀' ∈ chartCover` with `y ∈ innerShrunkChart x₀'` and
`‖localRep α x₀ y‖ ≤ M · ‖localRep α x₀' y‖`. -/
theorem exists_global_chart_transition_bound :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
      (x₀ : X), x₀ ∈ (chartCover : Finset X) →
        ∀ (y : X), y ∈ shrunkChart (X := X) x₀ →
          ∃ (x₀' : X) (_hx₀' : x₀' ∈ (chartCover : Finset X))
            (_hy' : y ∈ innerShrunkChart (X := X) x₀'),
            ‖localRep α x₀ y‖ ≤ M * ‖localRep α x₀' y‖ := by
  classical
  -- For each pair (x₀, x₀') ∈ chartCover², get the pairwise bound.
  -- Take max over the finite product.
  let pairs : Finset (X × X) := (chartCover : Finset X) ×ˢ (chartCover : Finset X)
  -- Define per-pair constant via Classical.choose from exists_pairwise_chart_transition_bound.
  let M_pair : X × X → ℝ := fun p =>
    if h : p.1 ∈ (chartCover : Finset X) ∧ p.2 ∈ (chartCover : Finset X) then
      Classical.choose (exists_pairwise_chart_transition_bound p.1 p.2 h.1 h.2)
    else 0
  have hM_pair_nn : ∀ p, 0 ≤ M_pair p := by
    intro p
    simp only [M_pair]
    split_ifs with h
    · exact (Classical.choose_spec (exists_pairwise_chart_transition_bound p.1 p.2 h.1 h.2)).1
    · exact le_refl 0
  -- M := sup over pairs. If pairs empty, M = 0. Not empty since chartCover nonempty.
  have hpairs_nonempty : pairs.Nonempty := by
    obtain ⟨x₀, hx₀⟩ := chartCover_nonempty (X := X)
    exact ⟨(x₀, x₀), Finset.mem_product.mpr ⟨hx₀, hx₀⟩⟩
  let M : ℝ := pairs.sup' hpairs_nonempty M_pair
  have hM_nn : 0 ≤ M := by
    obtain ⟨p, hp⟩ := hpairs_nonempty
    exact le_trans (hM_pair_nn p) (Finset.le_sup' _ hp)
  refine ⟨M, hM_nn, ?_⟩
  intro α x₀ hx₀ y hy_shrunk
  -- Get x₀' ∈ chartCover with y ∈ innerShrunkChart x₀' (inner cover).
  have hmem : y ∈ (Set.univ : Set X) := Set.mem_univ _
  rw [← iUnion_innerShrunkChart_chartCover_eq (X := X)] at hmem
  simp only [Set.mem_iUnion] at hmem
  obtain ⟨x₀', hx₀'mem, hy_inner⟩ := hmem
  refine ⟨x₀', hx₀'mem, hy_inner, ?_⟩
  -- Apply pairwise bound for (x₀, x₀').
  have hpair_bound := exists_pairwise_chart_transition_bound x₀ x₀' hx₀ hx₀'mem
  have hMpair_def : M_pair (x₀, x₀') =
      Classical.choose hpair_bound := by
    simp only [M_pair]
    rw [dif_pos ⟨hx₀, hx₀'mem⟩]
  have hMpair_spec := Classical.choose_spec hpair_bound
  have hbd := hMpair_spec.2 α y hy_shrunk hy_inner
  rw [← hMpair_def] at hbd
  have hle : M_pair (x₀, x₀') ≤ M :=
    Finset.le_sup' _ (Finset.mem_product.mpr ⟨hx₀, hx₀'mem⟩)
  calc ‖localRep α x₀ y‖
      ≤ M_pair (x₀, x₀') * ‖localRep α x₀' y‖ := hbd
    _ ≤ M * ‖localRep α x₀' y‖ :=
        mul_le_mul_of_nonneg_right hle (norm_nonneg _)

/-! ### `supNormK` form of the chart-transition bound -/

omit [ConnectedSpace X] in
/-- **Chart-transition supNormK bound.** There exists a universal
constant `M ≥ 0` such that for any α,
`supNormK α ≤ M · (max over chartCover of sSup of ‖localRep α x₀'·‖
  on innerShrunkChart x₀')`.

This is the supNormK form of `exists_global_chart_transition_bound`,
obtained by taking sup over y of the pointwise bound. -/
theorem exists_supNormK_le_const_sup_inner :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x)),
      HolomorphicOneForms.supNormK α ≤
        M * (chartCover : Finset X).sup' chartCover_nonempty
          (fun x₀' => sSup ((fun y : X => ‖localRep α x₀' y‖) ''
            innerShrunkChart (X := X) x₀')) := by
  obtain ⟨M, hMnn, hM⟩ := exists_global_chart_transition_bound (X := X)
  refine ⟨M, hMnn, fun α => ?_⟩
  -- supNormK α = max_{x₀ ∈ chartCover} sup_{y ∈ shrunkChart x₀} ‖localRep α x₀ y‖
  -- We want: this ≤ M * max_{x₀' ∈ chartCover} sup_{y ∈ innerShrunkChart x₀'} ‖localRep α x₀' y‖
  unfold HolomorphicOneForms.supNormK
  rw [Finset.sup'_le_iff]
  intro x₀ hx₀
  -- chartNormK α x₀ ≤ M * sup_{x₀'} sSup_{innerShrunkChart x₀'} |localRep α x₀' ·|
  unfold HolomorphicOneForms.chartNormK
  -- sSup ≤ M * (sup_{x₀'} sSup_{inner x₀'} ...)
  have hbdd : BddAbove ((fun y : X => ‖localRep α x₀ y‖) '' shrunkChart (X := X) x₀) :=
    HolomorphicOneForms.chartNormK_bddAbove α x₀
  -- If shrunkChart x₀ is empty, LHS = sSup (∅ : Set ℝ) = 0; RHS ≥ 0.
  by_cases hne : Set.Nonempty (shrunkChart (X := X) x₀)
  swap
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    simp only [hne, Set.image_empty, Real.sSup_empty]
    -- RHS is nonneg.
    apply mul_nonneg hMnn
    -- Finset.sup' of sSup of image terms.
    obtain ⟨x₀₀, hx₀₀⟩ := chartCover_nonempty (X := X)
    apply le_trans _ (Finset.le_sup' _ hx₀₀)
    -- Per-factor: sSup ≥ 0 (norms).
    by_cases hne' : Set.Nonempty (innerShrunkChart (X := X) x₀₀)
    · obtain ⟨z, hz⟩ := hne'
      have hz_img : ‖localRep α x₀₀ z‖ ∈
          (fun y => ‖localRep α x₀₀ y‖) '' innerShrunkChart (X := X) x₀₀ :=
        ⟨z, hz, rfl⟩
      have hbdd : BddAbove ((fun y => ‖localRep α x₀₀ y‖) '' innerShrunkChart (X := X) x₀₀) := by
        have := HolomorphicOneForms.chartNormK_bddAbove α x₀₀
        apply this.mono
        intro w ⟨z', hz', hzw'⟩
        exact ⟨z', innerShrunkChart_subset_shrunkChart x₀₀ hz', hzw'⟩
      exact le_trans (norm_nonneg _) (le_csSup hbdd hz_img)
    · rw [Set.not_nonempty_iff_eq_empty] at hne'
      simp [hne']
  apply csSup_le
  · obtain ⟨y, hy⟩ := hne
    exact ⟨‖localRep α x₀ y‖, y, hy, rfl⟩
  · rintro _ ⟨y, hy_shrunk, rfl⟩
    -- For y ∈ shrunkChart x₀: apply global bound to get x₀' and bound.
    obtain ⟨x₀', hx₀'mem, hy_inner, hbound⟩ := hM α x₀ hx₀ y hy_shrunk
    -- ‖localRep α x₀ y‖ ≤ M * ‖localRep α x₀' y‖.
    have h_inner_y : ‖localRep α x₀' y‖ ≤
        sSup ((fun z : X => ‖localRep α x₀' z‖) '' innerShrunkChart (X := X) x₀') := by
      apply le_csSup
      · -- BddAbove of image over innerShrunkChart
        have := HolomorphicOneForms.chartNormK_bddAbove α x₀'
        -- innerShrunkChart ⊂ shrunkChart, so image is a subset.
        have hsub : ((fun z : X => ‖localRep α x₀' z‖) '' innerShrunkChart (X := X) x₀') ⊆
            ((fun z : X => ‖localRep α x₀' z‖) '' shrunkChart (X := X) x₀') := by
          intro w ⟨z, hz, hzw⟩
          exact ⟨z, innerShrunkChart_subset_shrunkChart x₀' hz, hzw⟩
        exact this.mono hsub
      · exact ⟨y, hy_inner, rfl⟩
    -- And sSup_{inner x₀'} ≤ chartCover.sup' ... (sSup over innerShrunkChart x₀'').
    have h_finsup : sSup ((fun z : X => ‖localRep α x₀' z‖) '' innerShrunkChart (X := X) x₀') ≤
        (chartCover : Finset X).sup' chartCover_nonempty
          (fun x₀'' => sSup ((fun z : X => ‖localRep α x₀'' z‖) ''
            innerShrunkChart (X := X) x₀'')) :=
      Finset.le_sup' (f := fun x₀'' => sSup ((fun z : X => ‖localRep α x₀'' z‖) ''
        innerShrunkChart (X := X) x₀'')) hx₀'mem
    calc ‖localRep α x₀ y‖
        ≤ M * ‖localRep α x₀' y‖ := hbound
      _ ≤ M * sSup ((fun z : X => ‖localRep α x₀' z‖) ''
          innerShrunkChart (X := X) x₀') :=
          mul_le_mul_of_nonneg_left h_inner_y hMnn
      _ ≤ M * (chartCover : Finset X).sup' chartCover_nonempty _ :=
          mul_le_mul_of_nonneg_left h_finsup hMnn

end Jacobians.Montel
