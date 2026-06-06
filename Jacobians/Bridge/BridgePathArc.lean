import Jacobians.Bridge.KirovLineIntegral
import Jacobians.RiemannSurface.ArcAlgebra

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

namespace PathChartBallSubdivision

variable {P₀ P : X} {γ : Path P₀ P} (S : PathChartBallSubdivision γ)

omit [T2Space X] in
/-- A single endpoint-flat chart segment packaged as a strong analytic arc. -/
noncomputable def chartFlatAnalyticArc (n : ℕ) : AnalyticArc X where
  extend := (S.chartFlatPath n).extend
  continuous' := Path.continuous_extend _
  partition := {0, 1}
  partition_subset := by
    intro r hr
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl <;> simp
  zero_mem := by simp
  one_mem := by simp
  is_analytic_strong := by
    intro a ha b hb hab _hcons
    have ha01 : a = 0 ∨ a = 1 := by simpa using ha
    have hb01 : b = 0 ∨ b = 1 := by simpa using hb
    rcases ha01 with rfl | rfl
    · rcases hb01 with rfl | rfl
      · exact False.elim (lt_irrefl (0 : ℝ) hab)
      · refine ⟨{0, 1}, by simp, by simp, ?_, ?_⟩
        · intro r hr
          simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
            Set.mem_singleton_iff] at hr
          rcases hr with rfl | rfl <;> simp
        · intro s hs t ht hst _hτcons
          have hs01 : s = 0 ∨ s = 1 := by simpa using hs
          have ht01 : t = 0 ∨ t = 1 := by simpa using ht
          rcases hs01 with rfl | rfl
          · rcases ht01 with rfl | rfl
            · exact False.elim (lt_irrefl (0 : ℝ) hst)
            · let z₀ : ℂ := (chartAt ℂ (S.chart n)) (γ (S.t n))
              let z₁ : ℂ := (chartAt ℂ (S.chart n)) (γ (S.t (n + 1)))
              refine ⟨S.chart n, Set.univ, flatSegment z₀ z₁, isOpen_univ, ?_, ?_, ?_, ?_⟩
              · intro r _
                exact Set.mem_univ r
              · intro r _
                exact analyticAt_flatSegment z₀ z₁ r
              · intro r hr
                simpa [extChartAt_source] using
                  S.chartFlatPath_extend_mem_chart_source_of_mem_Icc n hr.2
              · intro r hr
                rw [extChartAt_coe, modelWithCornersSelf_coe]
                rw [Path.extend_apply _ hr.2]
                exact (chartAt ℂ (S.chart n)).right_inv
                  (S.flatSegment_mem_chart_target n hr.2)
          · rcases ht01 with rfl | rfl
            · linarith
            · exact False.elim (lt_irrefl (1 : ℝ) hst)
    · rcases hb01 with rfl | rfl
      · linarith
      · exact False.elim (lt_irrefl (1 : ℝ) hab)

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

private noncomputable def concatChartFlatPathAuxPartition : ℕ → Finset ℝ
  | 0 => {0, 1}
  | k + 1 => (concatChartFlatPathAuxPartition k).image (fun r : ℝ => r / 2) ∪ {1 / 2, 1}

private lemma concatChartFlatPathAuxPartition_subset (k : ℕ) :
    ↑(concatChartFlatPathAuxPartition k) ⊆ Set.Icc (0 : ℝ) 1 := by
  induction k with
  | zero =>
      intro r hr
      have hr' : r = 0 ∨ r = 1 := by
        simpa [concatChartFlatPathAuxPartition] using hr
      rcases hr' with rfl | rfl <;> norm_num
  | succ k ih =>
      intro r hr
      rw [concatChartFlatPathAuxPartition] at hr
      rcases Finset.mem_union.mp hr with himg | hright
      · rcases Finset.mem_image.mp himg with ⟨x, hx, rfl⟩
        have hx01 := ih hx
        constructor <;> nlinarith [hx01.1, hx01.2]
      · have hright' : r = 1 / 2 ∨ r = 1 := by
          simpa using hright
        rcases hright' with rfl | rfl <;> norm_num

private lemma concatChartFlatPathAuxPartition_zero_mem (k : ℕ) :
    (0 : ℝ) ∈ concatChartFlatPathAuxPartition k := by
  induction k with
  | zero =>
      simp [concatChartFlatPathAuxPartition]
  | succ k ih =>
      rw [concatChartFlatPathAuxPartition]
      exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_image.mpr ⟨0, ih, by norm_num⟩))

private lemma concatChartFlatPathAuxPartition_one_mem (k : ℕ) :
    (1 : ℝ) ∈ concatChartFlatPathAuxPartition k := by
  induction k with
  | zero =>
      simp [concatChartFlatPathAuxPartition]
  | succ k _ =>
      simp [concatChartFlatPathAuxPartition]

namespace PathChartBallSubdivision

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  {P₀ P : X} {γ : Path P₀ P} (S : PathChartBallSubdivision γ)

/-- Recursive analytic-arc package for the first `k + 1` flattened bridge pieces. -/
noncomputable def concatChartFlatPathAuxAnalyticArcData (k : ℕ) :
    {η : AnalyticArc X //
      η.extend 0 = γ (S.t 0) ∧
      η.extend 1 = γ (S.t (k + 1)) ∧
      η.partition = concatChartFlatPathAuxPartition k ∧
      η.extend = (S.concatChartFlatPathAux k).extend} := by
  induction k with
  | zero =>
      refine ⟨S.chartFlatAnalyticArc 0, ?_, ?_, ?_, ?_⟩
      · simp [chartFlatAnalyticArc]
      · simp [chartFlatAnalyticArc]
      · simp [chartFlatAnalyticArc, concatChartFlatPathAuxPartition]
      · rfl
  | succ k ih =>
      let η₁ : AnalyticArc X := ih.val
      let η₂ : AnalyticArc X := S.chartFlatAnalyticArc (k + 1)
      have hjoin : η₁.extend 1 = η₂.extend 0 := by
        rw [ih.property.2.1]
        simp [η₂, chartFlatAnalyticArc]
      refine ⟨η₁.trans η₂ hjoin, ?_, ?_, ?_, ?_⟩
      · simp [AnalyticArc.trans, η₁, ih.property.1]
      · simp [AnalyticArc.trans, η₂, chartFlatAnalyticArc]
        norm_num
      ·
        change (η₁.trans η₂ hjoin).partition = concatChartFlatPathAuxPartition (k + 1)
        simp [AnalyticArc.trans, η₁, η₂, ih.property.2.2.1, chartFlatAnalyticArc,
          concatChartFlatPathAuxPartition]
      ·
        funext r
        change (η₁.trans η₂ hjoin).extend r = (S.concatChartFlatPathAux (k + 1)).extend r
        by_cases hr : r ≤ (1 / 2 : ℝ)
        · have hr' : r ≤ (2 : ℝ)⁻¹ := by simpa [one_div] using hr
          rw [AnalyticArc.trans]
          simp [hr', η₁, η₂, ih.property.2.2.2, chartFlatAnalyticArc,
            concatChartFlatPathAux_succ,
            Path.extend_trans_of_le_half (S.concatChartFlatPathAux k)
              (S.chartFlatPath (k + 1)) hr]
        · have hr' : ¬ r ≤ (2 : ℝ)⁻¹ := by simpa [one_div] using hr
          have hhr : (1 / 2 : ℝ) ≤ r := le_of_lt (lt_of_not_ge hr)
          rw [AnalyticArc.trans]
          simp [hr', η₁, η₂, ih.property.2.2.2, chartFlatAnalyticArc,
            concatChartFlatPathAux_succ,
            Path.extend_trans_of_half_le (S.concatChartFlatPathAux k)
              (S.chartFlatPath (k + 1)) hhr]

/-- The analytic arc obtained by concatenating the first `k + 1` bridge pieces. -/
noncomputable def concatChartFlatPathAuxAnalyticArc (k : ℕ) : AnalyticArc X :=
  (S.concatChartFlatPathAuxAnalyticArcData k).val

theorem concatChartFlatPathAuxAnalyticArc_partition (k : ℕ) :
    (S.concatChartFlatPathAuxAnalyticArc k).partition = concatChartFlatPathAuxPartition k :=
  (S.concatChartFlatPathAuxAnalyticArcData k).property.2.2.1

theorem concatChartFlatPathAuxAnalyticArc_extend (k : ℕ) :
    (S.concatChartFlatPathAuxAnalyticArc k).extend = (S.concatChartFlatPathAux k).extend :=
  (S.concatChartFlatPathAuxAnalyticArcData k).property.2.2.2

end PathChartBallSubdivision

private lemma concatChartFlatPathAuxRegular_of_mem_Ioo_not_mem_partition
    (k : ℕ) {t : ℝ} (ht01 : t ∈ Set.Ioo (0 : ℝ) 1)
    (htnot : t ∉ concatChartFlatPathAuxPartition k) :
    PathChartBallSubdivision.concatChartFlatPathAuxRegular k t := by
  induction k generalizing t with
  | zero =>
      exact Or.inr (Or.inl ht01)
  | succ k ih =>
      have ht_ne_half : t ≠ 1 / 2 := by
        intro ht
        apply htnot
        subst t
        simp [concatChartFlatPathAuxPartition]
      rcases lt_or_gt_of_ne ht_ne_half with htlt | hthalf
      · refine Or.inl ⟨htlt, ih ?_ ?_⟩
        · constructor <;> nlinarith [ht01.1, htlt]
        · intro hmem
          apply htnot
          have ht_image :
              t ∈ (concatChartFlatPathAuxPartition k).image (fun r : ℝ => r / 2) := by
            exact Finset.mem_image.mpr ⟨2 * t, hmem, by ring⟩
          change t ∈ (concatChartFlatPathAuxPartition k).image (fun r : ℝ => r / 2) ∪
            {1 / 2, 1}
          exact Finset.mem_union.mpr (Or.inl ht_image)
      · refine Or.inr ⟨hthalf, ?_⟩
        exact Or.inr (Or.inl ⟨by nlinarith [hthalf], by nlinarith [ht01.2]⟩)

/-- The finite breakpoint set obtained from the chosen bridge-path subdivision. -/
noncomputable def bridgePathArcPartition (P₀ P : X) : Finset ℝ :=
  let γ : Path P₀ P := (exists_path P₀ P).some
  let S : PathChartBallSubdivision γ := (exists_pathChartBallSubdivision γ).some
  concatChartFlatPathAuxPartition S.lastIndex

theorem bridgePathArcPartition_subset (P₀ P : X) :
    ↑(bridgePathArcPartition (X := X) P₀ P) ⊆ Set.Icc (0 : ℝ) 1 := by
  let γ : Path P₀ P := (exists_path P₀ P).some
  let S : PathChartBallSubdivision γ := (exists_pathChartBallSubdivision γ).some
  change ↑(concatChartFlatPathAuxPartition S.lastIndex) ⊆ Set.Icc (0 : ℝ) 1
  exact concatChartFlatPathAuxPartition_subset S.lastIndex

theorem bridgePathArcPartition_zero_mem (P₀ P : X) :
    (0 : ℝ) ∈ bridgePathArcPartition (X := X) P₀ P := by
  let γ : Path P₀ P := (exists_path P₀ P).some
  let S : PathChartBallSubdivision γ := (exists_pathChartBallSubdivision γ).some
  change (0 : ℝ) ∈ concatChartFlatPathAuxPartition S.lastIndex
  exact concatChartFlatPathAuxPartition_zero_mem S.lastIndex

theorem bridgePathArcPartition_one_mem (P₀ P : X) :
    (1 : ℝ) ∈ bridgePathArcPartition (X := X) P₀ P := by
  let γ : Path P₀ P := (exists_path P₀ P).some
  let S : PathChartBallSubdivision γ := (exists_pathChartBallSubdivision γ).some
  change (1 : ℝ) ∈ concatChartFlatPathAuxPartition S.lastIndex
  exact concatChartFlatPathAuxPartition_one_mem S.lastIndex

theorem bridgePathImplRegular_of_mem_Ioo_not_mem_bridgePathArcPartition
    (P₀ P : X) {t : ℝ} (ht01 : t ∈ Set.Ioo (0 : ℝ) 1)
    (htnot : t ∉ (bridgePathArcPartition (X := X) P₀ P : Set ℝ)) :
    bridgePathImplRegular (X := X) P₀ P t := by
  let γ : Path P₀ P := (exists_path P₀ P).some
  let S : PathChartBallSubdivision γ := (exists_pathChartBallSubdivision γ).some
  change PathChartBallSubdivision.concatChartFlatPathAuxRegular S.lastIndex t
  apply concatChartFlatPathAuxRegular_of_mem_Ioo_not_mem_partition S.lastIndex ht01
  intro hmem
  apply htnot
  simpa [bridgePathArcPartition] using hmem

end BridgePathArcPartition

section BridgePathArc

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-- The bridge path packaged as a piecewise-real-analytic arc. -/
noncomputable def bridgePathArc (P₀ P : X) : AnalyticArc X where
  extend := bridgePathImpl (X := X) P₀ P
  continuous' := bridgePathImpl_continuous (X := X) P₀ P
  partition := bridgePathArcPartition (X := X) P₀ P
  partition_subset := bridgePathArcPartition_subset (X := X) P₀ P
  zero_mem := bridgePathArcPartition_zero_mem (X := X) P₀ P
  one_mem := bridgePathArcPartition_one_mem (X := X) P₀ P
  is_analytic_strong := by
    let γ : Path P₀ P := (exists_path P₀ P).some
    let S : PathChartBallSubdivision γ := (exists_pathChartBallSubdivision γ).some
    let η : AnalyticArc X := S.concatChartFlatPathAuxAnalyticArc S.lastIndex
    have hpart : η.partition = bridgePathArcPartition (X := X) P₀ P := by
      dsimp [η, bridgePathArcPartition]
      exact S.concatChartFlatPathAuxAnalyticArc_partition S.lastIndex
    have hext : η.extend = bridgePathImpl (X := X) P₀ P := by
      funext r
      change (S.concatChartFlatPathAuxAnalyticArc S.lastIndex).extend r =
        (S.concatChartFlatPath).extend r
      rw [congrFun (S.concatChartFlatPathAuxAnalyticArc_extend S.lastIndex) r]
      simp [PathChartBallSubdivision.concatChartFlatPath]
    simpa [hpart, hext] using η.is_analytic_strong

end BridgePathArc

end Jacobians.Bridge
