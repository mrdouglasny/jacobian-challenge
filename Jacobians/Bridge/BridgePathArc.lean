import Jacobians.Bridge.KirovLineIntegral
import Jacobians.RiemannSurface.AnalyticArc

/-!
# Analytic bridge-path helpers

This file collects the analyticity facts needed to package `bridgePath` as an
`AnalyticArc`.
-/

namespace Jacobians.Bridge

open scoped Manifold ContDiff Topology
open Filter
open Jacobians.RiemannSurface

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

omit [T2Space X] in
/-- Chart transitions between two `extChartAt` charts are real-analytic on their overlap. -/
lemma extChartAt_trans_analyticAt {p q : X} {z : ℂ}
    (hz : z ∈ (extChartAt 𝓘(ℂ) q).target)
    (hmem : (extChartAt 𝓘(ℂ) q).symm z ∈ (extChartAt 𝓘(ℂ) p).source) :
    AnalyticAt ℝ ((extChartAt 𝓘(ℂ) p) ∘ (extChartAt 𝓘(ℂ) q).symm) z := by
  have htransition_source :
      z ∈ ((extChartAt 𝓘(ℂ) q).symm ≫ extChartAt 𝓘(ℂ) p).source := by
    rw [PartialEquiv.trans_source]
    exact ⟨hz, hmem⟩
  have hcont :
      ContDiffWithinAt ℂ ω
        (extChartAt 𝓘(ℂ) p ∘ (extChartAt 𝓘(ℂ) q).symm)
        (Set.range ((𝓘(ℂ) : ModelWithCorners ℂ ℂ ℂ) : ℂ → ℂ)) z :=
    contDiffWithinAt_ext_coord_change (I := 𝓘(ℂ)) p q htransition_source
  have hcontAt :
      ContDiffAt ℂ ω
        (extChartAt 𝓘(ℂ) p ∘ (extChartAt 𝓘(ℂ) q).symm) z := by
    rw [← contDiffWithinAt_univ]
    simpa [modelWithCornersSelf_coe] using hcont
  exact hcontAt.analyticAt.restrictScalars (𝕜 := ℝ)

/-- The cubic flat reparameterization is real-analytic. -/
lemma analyticAt_flatReparam (t : ℝ) :
    AnalyticAt ℝ flatReparam t := by
  unfold flatReparam
  fun_prop

section FlatSegment

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Flat affine segments are real-analytic. -/
lemma analyticAt_flatSegment (a b : E) (t : ℝ) :
    AnalyticAt ℝ (flatSegment a b) t := by
  unfold flatSegment
  have hφ : AnalyticAt ℝ flatReparam t := analyticAt_flatReparam t
  exact ((analyticAt_const.sub hφ).smul analyticAt_const).add (hφ.smul analyticAt_const)

end FlatSegment

/-- Analyticity is preserved by the left branch of `Path.trans` away from the glue point. -/
lemma analyticAt_comp_pathTrans_extend_left_of_lt_half
    {Y F : Type*} [TopologicalSpace Y] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {x y z : Y} {f : Y → F} (γ₁ : Path x y) (γ₂ : Path y z)
    {t : ℝ} (ht : t < 1 / 2)
    (hf : AnalyticAt ℝ (f ∘ γ₁.extend) (2 * t)) :
    AnalyticAt ℝ (f ∘ (γ₁.trans γ₂).extend) t := by
  have hscale : AnalyticAt ℝ (fun u : ℝ => 2 * u) t := by
    fun_prop
  have hcomp : AnalyticAt ℝ ((f ∘ γ₁.extend) ∘ fun u : ℝ => 2 * u) t :=
    hf.comp hscale
  have heq :
      (f ∘ (γ₁.trans γ₂).extend) =ᶠ[𝓝 t]
        ((f ∘ γ₁.extend) ∘ fun u : ℝ => 2 * u) :=
    (pathTrans_extend_eventuallyEq_left_of_lt_half γ₁ γ₂ ht).mono fun u hu => by
      simp [Function.comp_def, hu]
  exact hcomp.congr heq.symm

/-- Analyticity is preserved by the right branch of `Path.trans` away from the glue point. -/
lemma analyticAt_comp_pathTrans_extend_right_of_half_lt
    {Y F : Type*} [TopologicalSpace Y] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {x y z : Y} {f : Y → F} (γ₁ : Path x y) (γ₂ : Path y z)
    {t : ℝ} (ht : 1 / 2 < t)
    (hf : AnalyticAt ℝ (f ∘ γ₂.extend) (2 * t - 1)) :
    AnalyticAt ℝ (f ∘ (γ₁.trans γ₂).extend) t := by
  have hscale : AnalyticAt ℝ (fun u : ℝ => 2 * u - 1) t := by
    fun_prop
  have hcomp : AnalyticAt ℝ ((f ∘ γ₂.extend) ∘ fun u : ℝ => 2 * u - 1) t :=
    AnalyticAt.comp_of_eq
      (𝕜 := ℝ) (g := f ∘ γ₂.extend) (f := fun u : ℝ => 2 * u - 1)
      (x := t) (y := 2 * t - 1) hf hscale rfl
  have heq :
      (f ∘ (γ₁.trans γ₂).extend) =ᶠ[𝓝 t]
        ((f ∘ γ₂.extend) ∘ fun u : ℝ => 2 * u - 1) :=
    (pathTrans_extend_eventuallyEq_right_of_half_lt γ₁ γ₂ ht).mono fun u hu => by
      simp [Function.comp_def, hu]
  exact hcomp.congr heq.symm

namespace PathChartBallSubdivision

variable {P₀ P : X} {γ : Path P₀ P} (S : PathChartBallSubdivision γ)

omit [T2Space X] [IsManifold 𝓘(ℂ) ω X] in
/-- In the interior of a local piece, its fixed subdivision-chart coordinate is analytic. -/
lemma chartFlatPath_extChartAt_chart_analyticAt_of_mem_Ioo
    (n : ℕ) {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    AnalyticAt ℝ
      ((extChartAt 𝓘(ℂ) (S.chart n)) ∘ (S.chartFlatPath n).extend) s := by
  let a : ℂ := (chartAt ℂ (S.chart n)) (γ (S.t n))
  let b : ℂ := (chartAt ℂ (S.chart n)) (γ (S.t (n + 1)))
  have hflat : AnalyticAt ℝ (flatSegment a b) s :=
    analyticAt_flatSegment a b s
  have heq :
      ((extChartAt 𝓘(ℂ) (S.chart n)) ∘ (S.chartFlatPath n).extend) =ᶠ[𝓝 s]
        flatSegment a b := by
    simpa [a, b, extChartAt_coe, modelWithCornersSelf_coe] using
      S.chartFlatPath_chart_eventuallyEq_flatSegment_of_mem_Ioo n hs
  exact hflat.congr heq.symm

omit [T2Space X] [IsManifold 𝓘(ℂ) ω X] in
/-- Away from its two endpoints, a local piece is analytic in its fixed subdivision chart. -/
lemma chartFlatPath_extChartAt_chart_analyticAt_of_regular
    (n : ℕ) {s : ℝ} (hs : flatPieceRegular s) :
    AnalyticAt ℝ
      ((extChartAt 𝓘(ℂ) (S.chart n)) ∘ (S.chartFlatPath n).extend) s := by
  rcases hs with hs | hs | hs
  · have heq :
        ((extChartAt 𝓘(ℂ) (S.chart n)) ∘ (S.chartFlatPath n).extend) =ᶠ[𝓝 s]
          fun _ : ℝ => (extChartAt 𝓘(ℂ) (S.chart n)) (γ (S.t n)) := by
      filter_upwards [eventually_lt_nhds hs] with u hu
      simp [Path.extend_of_le_zero _ hu.le]
    exact (analyticAt_const :
      AnalyticAt ℝ
        (fun _ : ℝ => (extChartAt 𝓘(ℂ) (S.chart n)) (γ (S.t n))) s).congr heq.symm
  · exact S.chartFlatPath_extChartAt_chart_analyticAt_of_mem_Ioo n hs
  · have heq :
        ((extChartAt 𝓘(ℂ) (S.chart n)) ∘ (S.chartFlatPath n).extend) =ᶠ[𝓝 s]
          fun _ : ℝ => (extChartAt 𝓘(ℂ) (S.chart n)) (γ (S.t (n + 1))) := by
      filter_upwards [eventually_gt_nhds hs] with u hu
      simp [Path.extend_of_one_le _ hu.le]
    exact (analyticAt_const :
      AnalyticAt ℝ
        (fun _ : ℝ => (extChartAt 𝓘(ℂ) (S.chart n)) (γ (S.t (n + 1)))) s).congr heq.symm

omit [T2Space X] in
/-- Away from its two endpoints, a local piece is analytic in the chart centered at its value. -/
lemma chartFlatPath_extChartAt_current_analyticAt_of_regular
    (n : ℕ) {s : ℝ} (hs : flatPieceRegular s) :
    AnalyticAt ℝ
      (fun r : ℝ =>
        (extChartAt 𝓘(ℂ) ((S.chartFlatPath n).extend s)) ((S.chartFlatPath n).extend r)) s := by
  let x : X := (S.chartFlatPath n).extend s
  let y : X := S.chart n
  have hsource_eventually :
      ∀ᶠ u in 𝓝 s,
        (S.chartFlatPath n).extend u ∈ (chartAt ℂ y).source := by
    simpa [y] using S.chartFlatPath_extend_eventually_mem_chart_source_of_regular n hs
  have hsource : x ∈ (extChartAt 𝓘(ℂ) y).source := by
    have hx_chart : x ∈ (chartAt ℂ y).source := by
      simpa [x] using hsource_eventually.self_of_nhds
    simpa [extChartAt_source] using hx_chart
  have hfixed :
      AnalyticAt ℝ
        ((extChartAt 𝓘(ℂ) y) ∘ (S.chartFlatPath n).extend) s := by
    simpa [y] using S.chartFlatPath_extChartAt_chart_analyticAt_of_regular n hs
  have hz : (extChartAt 𝓘(ℂ) y) x ∈ (extChartAt 𝓘(ℂ) y).target :=
    (extChartAt 𝓘(ℂ) y).map_source hsource
  have hleft :
      (extChartAt 𝓘(ℂ) y).symm ((extChartAt 𝓘(ℂ) y) x) = x :=
    (extChartAt 𝓘(ℂ) y).left_inv hsource
  have hmem :
      (extChartAt 𝓘(ℂ) y).symm ((extChartAt 𝓘(ℂ) y) x) ∈
        (extChartAt 𝓘(ℂ) x).source := by
    rw [hleft]
    exact mem_extChartAt_source x
  have houter :
      AnalyticAt ℝ
        ((extChartAt 𝓘(ℂ) x) ∘ (extChartAt 𝓘(ℂ) y).symm)
        (((extChartAt 𝓘(ℂ) y) ∘ (S.chartFlatPath n).extend) s) := by
    simpa [x, Function.comp_def] using
      extChartAt_trans_analyticAt (p := x) (q := y)
        (z := (extChartAt 𝓘(ℂ) y) x) hz hmem
  have hcomp :
      AnalyticAt ℝ
        (((extChartAt 𝓘(ℂ) x) ∘ (extChartAt 𝓘(ℂ) y).symm) ∘
          ((extChartAt 𝓘(ℂ) y) ∘ (S.chartFlatPath n).extend)) s :=
    houter.comp hfixed
  have heq :
      (fun r : ℝ => (extChartAt 𝓘(ℂ) x) ((S.chartFlatPath n).extend r)) =ᶠ[𝓝 s]
        (((extChartAt 𝓘(ℂ) x) ∘ (extChartAt 𝓘(ℂ) y).symm) ∘
          ((extChartAt 𝓘(ℂ) y) ∘ (S.chartFlatPath n).extend)) := by
    filter_upwards [hsource_eventually] with u hu_chart
    dsimp only [Function.comp_apply]
    change (chartAt ℂ x) ((S.chartFlatPath n).extend u) =
      (chartAt ℂ x)
        ((chartAt ℂ y).symm ((chartAt ℂ y) ((S.chartFlatPath n).extend u)))
    rw [(chartAt ℂ y).left_inv hu_chart]
  simpa [x] using hcomp.congr heq.symm

omit [T2Space X] in
/-- Recursive chart-flat concatenations are analytic at regular, non-glue parameters. -/
lemma concatChartFlatPathAux_extChartAt_current_analyticAt_of_regular
    (k : ℕ) {t : ℝ} (ht : concatChartFlatPathAuxRegular k t) :
    AnalyticAt ℝ
      (fun r : ℝ =>
        (extChartAt 𝓘(ℂ) ((S.concatChartFlatPathAux k).extend t))
          ((S.concatChartFlatPathAux k).extend r)) t := by
  induction k generalizing t with
  | zero =>
      simpa using S.chartFlatPath_extChartAt_current_analyticAt_of_regular 0 ht
  | succ k ih =>
      rcases ht with hleft | hright
      · rcases hleft with ⟨ht_half, ht_regular⟩
        have hcenter :
            ((S.concatChartFlatPathAux k).trans (S.chartFlatPath (k + 1))).extend t =
              (S.concatChartFlatPathAux k).extend (2 * t) := by
          exact
            Path.extend_trans_of_le_half
              (S.concatChartFlatPathAux k) (S.chartFlatPath (k + 1)) ht_half.le
        have hrec :
            AnalyticAt ℝ
              (fun r : ℝ =>
                (extChartAt 𝓘(ℂ) ((S.concatChartFlatPathAux k).extend (2 * t)))
                  ((S.concatChartFlatPathAux k).extend r)) (2 * t) :=
          ih ht_regular
        have hrec' :
            AnalyticAt ℝ
              (fun r : ℝ =>
                (extChartAt 𝓘(ℂ) ((S.concatChartFlatPathAux (k + 1)).extend t))
                  ((S.concatChartFlatPathAux k).extend r)) (2 * t) := by
          simpa [concatChartFlatPathAux_succ, hcenter] using hrec
        simpa [concatChartFlatPathAux_succ] using
          analyticAt_comp_pathTrans_extend_left_of_lt_half
            (S.concatChartFlatPathAux k) (S.chartFlatPath (k + 1))
            (f := fun x : X =>
              (extChartAt 𝓘(ℂ) ((S.concatChartFlatPathAux (k + 1)).extend t)) x)
            ht_half hrec'
      · rcases hright with ⟨ht_half, ht_regular⟩
        have hcenter :
            ((S.concatChartFlatPathAux k).trans (S.chartFlatPath (k + 1))).extend t =
              (S.chartFlatPath (k + 1)).extend (2 * t - 1) := by
          exact
            Path.extend_trans_of_half_le
              (S.concatChartFlatPathAux k) (S.chartFlatPath (k + 1)) ht_half.le
        have hpiece :
            AnalyticAt ℝ
              (fun r : ℝ =>
                (extChartAt 𝓘(ℂ) ((S.chartFlatPath (k + 1)).extend (2 * t - 1)))
                  ((S.chartFlatPath (k + 1)).extend r)) (2 * t - 1) :=
          S.chartFlatPath_extChartAt_current_analyticAt_of_regular (k + 1) ht_regular
        have hpiece' :
            AnalyticAt ℝ
              (fun r : ℝ =>
                (extChartAt 𝓘(ℂ) ((S.concatChartFlatPathAux (k + 1)).extend t))
                  ((S.chartFlatPath (k + 1)).extend r)) (2 * t - 1) := by
          simpa [concatChartFlatPathAux_succ, hcenter] using hpiece
        simpa [concatChartFlatPathAux_succ] using
          analyticAt_comp_pathTrans_extend_right_of_half_lt
            (S.concatChartFlatPathAux k) (S.chartFlatPath (k + 1))
            (f := fun x : X =>
              (extChartAt 𝓘(ℂ) ((S.concatChartFlatPathAux (k + 1)).extend t)) x)
            ht_half hpiece'

omit [T2Space X] in
/-- The full chart-flat replacement is analytic at regular, non-glue parameters. -/
lemma concatChartFlatPath_extChartAt_current_analyticAt_of_regular
    {t : ℝ} (ht : concatChartFlatPathAuxRegular S.lastIndex t) :
    AnalyticAt ℝ
      (fun r : ℝ =>
        (extChartAt 𝓘(ℂ) ((S.concatChartFlatPath).extend t))
          ((S.concatChartFlatPath).extend r)) t := by
  simpa [concatChartFlatPath] using
    S.concatChartFlatPathAux_extChartAt_current_analyticAt_of_regular S.lastIndex ht

end PathChartBallSubdivision

/-- The concrete bridge path is analytic at regular, non-glue parameters. -/
theorem bridgePathImpl_extChartAt_current_analyticAt_of_regular
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (P₀ P : X) {t : ℝ}
    (ht : bridgePathImplRegular (X := X) P₀ P t) :
    AnalyticAt ℝ
      (fun r : ℝ =>
        (extChartAt 𝓘(ℂ) (bridgePathImpl (X := X) P₀ P t))
          (bridgePathImpl (X := X) P₀ P r)) t := by
  let γ : Path P₀ P := (exists_path P₀ P).some
  let S : PathChartBallSubdivision γ := (exists_pathChartBallSubdivision γ).some
  change
    AnalyticAt ℝ
      (fun r : ℝ =>
        (extChartAt 𝓘(ℂ) ((S.concatChartFlatPath).extend t))
          ((S.concatChartFlatPath).extend r)) t
  change PathChartBallSubdivision.concatChartFlatPathAuxRegular S.lastIndex t at ht
  exact S.concatChartFlatPath_extChartAt_current_analyticAt_of_regular ht

section BridgePathArcPartition

variable {X : Type*} [TopologicalSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]

/-- The finite breakpoint set obtained from the chosen bridge-path subdivision. -/
noncomputable def bridgePathArcPartition (P₀ P : X) : Finset ℝ :=
  let γ : Path P₀ P := (exists_path P₀ P).some
  let S : PathChartBallSubdivision γ := (exists_pathChartBallSubdivision γ).some
  Finset.image
    (fun i : Fin (S.lastIndex + 1) => ((S.breakpoints i : unitInterval) : ℝ))
    Finset.univ

theorem bridgePathArcPartition_subset (P₀ P : X) :
    ↑(bridgePathArcPartition (X := X) P₀ P) ⊆ Set.Icc (0 : ℝ) 1 := by
  classical
  let γ : Path P₀ P := (exists_path P₀ P).some
  let S : PathChartBallSubdivision γ := (exists_pathChartBallSubdivision γ).some
  change
    ↑(Finset.image
      (fun i : Fin (S.lastIndex + 1) => ((S.breakpoints i : unitInterval) : ℝ))
      Finset.univ) ⊆ Set.Icc (0 : ℝ) 1
  intro r hr
  rcases Finset.mem_image.mp hr with ⟨i, _hi, rfl⟩
  exact (S.breakpoints i).2

theorem bridgePathArcPartition_zero_mem (P₀ P : X) :
    (0 : ℝ) ∈ bridgePathArcPartition (X := X) P₀ P := by
  classical
  let γ : Path P₀ P := (exists_path P₀ P).some
  let S : PathChartBallSubdivision γ := (exists_pathChartBallSubdivision γ).some
  change
    (0 : ℝ) ∈ Finset.image
      (fun i : Fin (S.lastIndex + 1) => ((S.breakpoints i : unitInterval) : ℝ))
      Finset.univ
  refine Finset.mem_image.mpr ⟨⟨0, Nat.succ_pos S.lastIndex⟩, by simp, ?_⟩
  exact congrArg Subtype.val (S.breakpoints_zero)

theorem bridgePathArcPartition_one_mem (P₀ P : X) :
    (1 : ℝ) ∈ bridgePathArcPartition (X := X) P₀ P := by
  classical
  let γ : Path P₀ P := (exists_path P₀ P).some
  let S : PathChartBallSubdivision γ := (exists_pathChartBallSubdivision γ).some
  change
    (1 : ℝ) ∈ Finset.image
      (fun i : Fin (S.lastIndex + 1) => ((S.breakpoints i : unitInterval) : ℝ))
      Finset.univ
  refine Finset.mem_image.mpr
    ⟨⟨S.lastIndex, Nat.lt_succ_self S.lastIndex⟩, by simp, ?_⟩
  exact congrArg Subtype.val (S.breakpoints_last)

end BridgePathArcPartition

end Jacobians.Bridge
