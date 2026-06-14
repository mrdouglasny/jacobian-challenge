/-
Multi-chart path integrals along analytic arcs.

This is milestone L1-a of the loop-integral discharge plan: define the
partitioned integral of a holomorphic 1-form along an analytic arc and prove
linearity in the form.  Chart/partition independence is deliberately left for
the later L1-b milestone.
-/
import Submission.Jacobians.RiemannSurface.ChartPartition
import Submission.Jacobians.RiemannSurface.PathIntegral

namespace Jacobians.RiemannSurface

open scoped Manifold Topology
open scoped ContDiff
open intervalIntegral MeasureTheory

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-- **Chart-local segment integral.** This is the subinterval version of
`pathIntegralOnChart`, integrating the chart expression over `a..b` and using
the open segment `Ioo a b` for the derivative-within set. -/
noncomputable def pathIntegralOnChartSeg (γ : AnalyticArc X) (p : X)
    (a b : ℝ) (form : HolomorphicOneForm X) : ℂ :=
  ∫ r in a..b,
    form.coeff p ((extChartAt 𝓘(ℂ) p) (γ.extend r)) *
      derivWithin (fun s : ℝ => (extChartAt 𝓘(ℂ) p) (γ.extend s))
        (Set.Ioo a b) r

/-- The segment integral on `[0, 1]` is definitionally the existing
single-chart integral. -/
@[simp]
theorem pathIntegralOnChartSeg_zero_one (γ : AnalyticArc X) (p : X)
    (form : HolomorphicOneForm X) :
    pathIntegralOnChartSeg γ p 0 1 form = pathIntegralOnChart γ p form := rfl

/-- A finite partition of `[0, 1]` whose closed cells are contained in selected
chart sources along `γ`. -/
structure ChartSubordinatePartition (γ : AnalyticArc X) where
  /-- Number of cells in the partition. -/
  n : ℕ
  /-- Partition points, indexed from `0` to `n`. -/
  t : Fin (n + 1) → ℝ
  /-- Chart centers for the `n` cells. -/
  p : Fin n → X
  /-- The first partition point is `0`. -/
  t_zero : t 0 = 0
  /-- The last partition point is `1`. -/
  t_last : t (Fin.last n) = 1
  /-- The partition points are monotone. -/
  t_mono : Monotone t
  /-- Each closed cell maps into the source of its selected chart. -/
  mem_source : ∀ i : Fin n, ∀ s ∈ Set.Icc (t i.castSucc) (t i.succ),
    γ.extend s ∈ (chartAt ℂ (p i)).source

namespace ChartSubordinatePartition

/-- L0 supplies at least one chart-subordinate partition for every analytic
arc. -/
instance instNonempty (γ : AnalyticArc X) : Nonempty (ChartSubordinatePartition γ) := by
  obtain ⟨n, t, p, ht_zero, ht_last, ht_mono, hmem⟩ :=
    exists_chart_subordinate_partition γ
  exact ⟨
    { n := n
      t := t
      p := p
      t_zero := ht_zero
      t_last := ht_last
      t_mono := ht_mono
      mem_source := hmem }⟩

end ChartSubordinatePartition

/-- The multi-chart integral over a fixed chart-subordinate partition: sum the
chart-local segment integrals over all cells. -/
noncomputable def pathIntegralOverPartition (γ : AnalyticArc X)
    (P : ChartSubordinatePartition γ) (form : HolomorphicOneForm X) : ℂ :=
  ∑ i : Fin P.n,
    pathIntegralOnChartSeg γ (P.p i) (P.t i.castSucc) (P.t i.succ) form

/-- The milestone L1-a path integral along an analytic arc.  It chooses an
arbitrary L0 chart-subordinate partition; independence of this choice is the
separate L1-b theorem and is not asserted here. -/
noncomputable def pathIntegralAnalyticArc (γ : AnalyticArc X)
    (form : HolomorphicOneForm X) : ℂ :=
  pathIntegralOverPartition γ (Classical.arbitrary (ChartSubordinatePartition γ)) form

/-- Additivity of the chart-local segment integral in the 1-form, with the same
integrability hypotheses as the existing Kirov-style line-integral API. -/
theorem pathIntegralOnChartSeg_add (γ : AnalyticArc X) (p : X) (a b : ℝ)
    (form₁ form₂ : HolomorphicOneForm X)
    (h₁ : IntervalIntegrable
      (fun r : ℝ =>
        form₁.coeff p ((extChartAt 𝓘(ℂ) p) (γ.extend r)) *
          derivWithin (fun s : ℝ => (extChartAt 𝓘(ℂ) p) (γ.extend s))
            (Set.Ioo a b) r)
      MeasureTheory.volume a b)
    (h₂ : IntervalIntegrable
      (fun r : ℝ =>
        form₂.coeff p ((extChartAt 𝓘(ℂ) p) (γ.extend r)) *
          derivWithin (fun s : ℝ => (extChartAt 𝓘(ℂ) p) (γ.extend s))
            (Set.Ioo a b) r)
      MeasureTheory.volume a b) :
    pathIntegralOnChartSeg γ p a b (form₁ + form₂) =
      pathIntegralOnChartSeg γ p a b form₁ +
        pathIntegralOnChartSeg γ p a b form₂ := by
  unfold pathIntegralOnChartSeg
  have h_pw : ∀ r : ℝ,
      (form₁ + form₂).coeff p ((extChartAt 𝓘(ℂ) p) (γ.extend r)) *
          derivWithin (fun s : ℝ => (extChartAt 𝓘(ℂ) p) (γ.extend s))
            (Set.Ioo a b) r =
        form₁.coeff p ((extChartAt 𝓘(ℂ) p) (γ.extend r)) *
            derivWithin (fun s : ℝ => (extChartAt 𝓘(ℂ) p) (γ.extend s))
              (Set.Ioo a b) r +
          form₂.coeff p ((extChartAt 𝓘(ℂ) p) (γ.extend r)) *
            derivWithin (fun s : ℝ => (extChartAt 𝓘(ℂ) p) (γ.extend s))
              (Set.Ioo a b) r := by
    intro r
    simp [add_mul]
  simp_rw [h_pw]
  exact intervalIntegral.integral_add h₁ h₂

/-- Scalar homogeneity of the chart-local segment integral in the 1-form. -/
theorem pathIntegralOnChartSeg_smul (γ : AnalyticArc X) (p : X) (a b : ℝ)
    (c : ℂ) (form : HolomorphicOneForm X) :
    pathIntegralOnChartSeg γ p a b (c • form) =
      c * pathIntegralOnChartSeg γ p a b form := by
  unfold pathIntegralOnChartSeg
  have h_pw : ∀ r : ℝ,
      (c • form).coeff p ((extChartAt 𝓘(ℂ) p) (γ.extend r)) *
          derivWithin (fun s : ℝ => (extChartAt 𝓘(ℂ) p) (γ.extend s))
            (Set.Ioo a b) r =
        c *
          (form.coeff p ((extChartAt 𝓘(ℂ) p) (γ.extend r)) *
            derivWithin (fun s : ℝ => (extChartAt 𝓘(ℂ) p) (γ.extend s))
              (Set.Ioo a b) r) := by
    intro r
    simp [mul_assoc]
  simp_rw [h_pw]
  exact intervalIntegral.integral_const_mul c _

/-- Additivity of the fixed-partition integral in the 1-form. -/
theorem pathIntegralOverPartition_add (γ : AnalyticArc X)
    (P : ChartSubordinatePartition γ) (form₁ form₂ : HolomorphicOneForm X)
    (h₁ : ∀ i : Fin P.n, IntervalIntegrable
      (fun r : ℝ =>
        form₁.coeff (P.p i) ((extChartAt 𝓘(ℂ) (P.p i)) (γ.extend r)) *
          derivWithin (fun s : ℝ => (extChartAt 𝓘(ℂ) (P.p i)) (γ.extend s))
            (Set.Ioo (P.t i.castSucc) (P.t i.succ)) r)
      MeasureTheory.volume (P.t i.castSucc) (P.t i.succ))
    (h₂ : ∀ i : Fin P.n, IntervalIntegrable
      (fun r : ℝ =>
        form₂.coeff (P.p i) ((extChartAt 𝓘(ℂ) (P.p i)) (γ.extend r)) *
          derivWithin (fun s : ℝ => (extChartAt 𝓘(ℂ) (P.p i)) (γ.extend s))
            (Set.Ioo (P.t i.castSucc) (P.t i.succ)) r)
      MeasureTheory.volume (P.t i.castSucc) (P.t i.succ)) :
    pathIntegralOverPartition γ P (form₁ + form₂) =
      pathIntegralOverPartition γ P form₁ + pathIntegralOverPartition γ P form₂ := by
  unfold pathIntegralOverPartition
  calc
    ∑ i : Fin P.n,
        pathIntegralOnChartSeg γ (P.p i) (P.t i.castSucc) (P.t i.succ)
          (form₁ + form₂) =
        ∑ i : Fin P.n,
          (pathIntegralOnChartSeg γ (P.p i) (P.t i.castSucc) (P.t i.succ) form₁ +
            pathIntegralOnChartSeg γ (P.p i) (P.t i.castSucc) (P.t i.succ) form₂) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      exact pathIntegralOnChartSeg_add γ (P.p i) (P.t i.castSucc) (P.t i.succ)
        form₁ form₂ (h₁ i) (h₂ i)
    _ =
        (∑ i : Fin P.n,
          pathIntegralOnChartSeg γ (P.p i) (P.t i.castSucc) (P.t i.succ) form₁) +
        (∑ i : Fin P.n,
          pathIntegralOnChartSeg γ (P.p i) (P.t i.castSucc) (P.t i.succ) form₂) := by
      exact Finset.sum_add_distrib

/-- Scalar homogeneity of the fixed-partition integral in the 1-form. -/
theorem pathIntegralOverPartition_smul (γ : AnalyticArc X)
    (P : ChartSubordinatePartition γ) (c : ℂ) (form : HolomorphicOneForm X) :
    pathIntegralOverPartition γ P (c • form) =
      c * pathIntegralOverPartition γ P form := by
  unfold pathIntegralOverPartition
  calc
    ∑ i : Fin P.n,
        pathIntegralOnChartSeg γ (P.p i) (P.t i.castSucc) (P.t i.succ) (c • form) =
        ∑ i : Fin P.n,
          c * pathIntegralOnChartSeg γ (P.p i) (P.t i.castSucc) (P.t i.succ) form := by
      refine Finset.sum_congr rfl ?_
      intro i _
      exact pathIntegralOnChartSeg_smul γ (P.p i) (P.t i.castSucc) (P.t i.succ)
        c form
    _ =
        c *
          ∑ i : Fin P.n,
            pathIntegralOnChartSeg γ (P.p i) (P.t i.castSucc) (P.t i.succ) form := by
      exact (Finset.mul_sum (s := Finset.univ)
        (f := fun i : Fin P.n =>
          pathIntegralOnChartSeg γ (P.p i) (P.t i.castSucc) (P.t i.succ) form)
        c).symm

/-- Additivity of the analytic-arc integral in the 1-form.  The hypotheses are
the per-cell integrability assumptions on the arbitrary L0 partition chosen by
`pathIntegralAnalyticArc`. -/
theorem pathIntegralAnalyticArc_add (γ : AnalyticArc X)
    (form₁ form₂ : HolomorphicOneForm X)
    (h₁ :
      ∀ i : Fin (Classical.arbitrary (ChartSubordinatePartition γ)).n,
        IntervalIntegrable
      (fun r : ℝ =>
        form₁.coeff ((Classical.arbitrary (ChartSubordinatePartition γ)).p i)
          ((extChartAt 𝓘(ℂ) ((Classical.arbitrary (ChartSubordinatePartition γ)).p i))
            (γ.extend r)) *
          derivWithin
            (fun s : ℝ =>
              (extChartAt 𝓘(ℂ)
                ((Classical.arbitrary (ChartSubordinatePartition γ)).p i))
                (γ.extend s))
            (Set.Ioo
              ((Classical.arbitrary (ChartSubordinatePartition γ)).t i.castSucc)
              ((Classical.arbitrary (ChartSubordinatePartition γ)).t i.succ)) r)
      MeasureTheory.volume
        ((Classical.arbitrary (ChartSubordinatePartition γ)).t i.castSucc)
        ((Classical.arbitrary (ChartSubordinatePartition γ)).t i.succ))
    (h₂ :
      ∀ i : Fin (Classical.arbitrary (ChartSubordinatePartition γ)).n,
        IntervalIntegrable
      (fun r : ℝ =>
        form₂.coeff ((Classical.arbitrary (ChartSubordinatePartition γ)).p i)
          ((extChartAt 𝓘(ℂ) ((Classical.arbitrary (ChartSubordinatePartition γ)).p i))
            (γ.extend r)) *
          derivWithin
            (fun s : ℝ =>
              (extChartAt 𝓘(ℂ)
                ((Classical.arbitrary (ChartSubordinatePartition γ)).p i))
                (γ.extend s))
            (Set.Ioo
              ((Classical.arbitrary (ChartSubordinatePartition γ)).t i.castSucc)
              ((Classical.arbitrary (ChartSubordinatePartition γ)).t i.succ)) r)
      MeasureTheory.volume
        ((Classical.arbitrary (ChartSubordinatePartition γ)).t i.castSucc)
        ((Classical.arbitrary (ChartSubordinatePartition γ)).t i.succ)) :
    pathIntegralAnalyticArc γ (form₁ + form₂) =
      pathIntegralAnalyticArc γ form₁ + pathIntegralAnalyticArc γ form₂ := by
  unfold pathIntegralAnalyticArc
  exact pathIntegralOverPartition_add γ
    (Classical.arbitrary (ChartSubordinatePartition γ)) form₁ form₂
    h₁ h₂

/-- Scalar homogeneity of the analytic-arc integral in the 1-form. -/
theorem pathIntegralAnalyticArc_smul (γ : AnalyticArc X) (c : ℂ)
    (form : HolomorphicOneForm X) :
    pathIntegralAnalyticArc γ (c • form) =
      c * pathIntegralAnalyticArc γ form := by
  unfold pathIntegralAnalyticArc
  exact pathIntegralOverPartition_smul γ
    (Classical.arbitrary (ChartSubordinatePartition γ)) c form

end Jacobians.RiemannSurface
