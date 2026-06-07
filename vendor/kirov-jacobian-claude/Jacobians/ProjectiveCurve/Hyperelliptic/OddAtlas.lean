/-
# HyperellipticOdd atlas — entry point (Phases OA3 + OA4)

Assembles `Phase OA1` (affine charts via implicit function theorem on
the smooth loci) and `Phase OA2` (chart at infinity via the local
uniformizer `t = y / x^{g+1}`) into:

* `instance : ChartedSpace ℂ (HyperellipticOdd H h)`
* `instance : IsManifold 𝓘(ℂ) ω (HyperellipticOdd H h)`

Once these compile, the two **temporary `axiom`s** at the top of
`Jacobians/Extensions/Hyperelliptic.lean` (OA4) can be deleted; instance
resolution picks up the real ones from this file.

See `docs/hyperelliptic-odd-atlas-plan.md`.
-/

import Jacobians.ProjectiveCurve.Hyperelliptic.OddAtlas.AffineChart
import Jacobians.ProjectiveCurve.Hyperelliptic.OddAtlas.InfinityChart
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

namespace Jacobians.ProjectiveCurve.HyperellipticOdd

open scoped Manifold ContDiff Topology

variable {H : HyperellipticData} {h : Odd H.f.natDegree}

/-- Affine charts on `HyperellipticAffine H` lifted along the open embedding
into the one-point compactification. -/
noncomputable def affineLiftChart (p : HyperellipticAffine H) :
    OpenPartialHomeomorph (HyperellipticOdd H h) ℂ :=
  (ChartedSpace.chartAt p).lift_openEmbedding
    (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H))

@[simp] theorem affineLiftChart_source (p : HyperellipticAffine H) :
    (affineLiftChart (H := H) (h := h) p).source =
      ((↑) : HyperellipticAffine H → OnePoint (HyperellipticAffine H)) ''
        (ChartedSpace.chartAt p : OpenPartialHomeomorph (HyperellipticAffine H) ℂ).source :=
  rfl

theorem mem_affineLiftChart_source (p : HyperellipticAffine H) :
    ((p : HyperellipticAffine H) : OnePoint (HyperellipticAffine H)) ∈
      (affineLiftChart (H := H) (h := h) p).source := by
  rw [affineLiftChart_source]
  exact ⟨p, ChartedSpace.mem_chart_source p, rfl⟩

/-- Preferred chart on `HyperellipticOdd H h`: the infinity chart at `∞`,
and the lifted affine chart on affine points. -/
noncomputable def chartAt : HyperellipticOdd H h →
    OpenPartialHomeomorph (HyperellipticOdd H h) ℂ :=
  OnePoint.rec (infinityChart H h) (fun p => affineLiftChart (H := H) (h := h) p)

@[simp] theorem chartAt_infty :
    chartAt (H := H) (h := h) (OnePoint.infty : HyperellipticOdd H h) = infinityChart H h :=
  rfl

@[simp] theorem chartAt_coe (p : HyperellipticAffine H) :
    chartAt (H := H) (h := h) ((p : HyperellipticAffine H) : OnePoint (HyperellipticAffine H)) =
      affineLiftChart (H := H) (h := h) p :=
  rfl

theorem affineLiftChart_compat (p q : HyperellipticAffine H) :
    ContDiffOn ℂ ω
      (((affineLiftChart (H := H) (h := h) p).symm.trans
          (affineLiftChart (H := H) (h := h) q)) : ℂ → ℂ)
      ((affineLiftChart (H := H) (h := h) p).symm.trans
        (affineLiftChart (H := H) (h := h) q)).source := by
  have hEq :
      (affineLiftChart (H := H) (h := h) p).symm.trans (affineLiftChart (H := H) (h := h) q) =
        (ChartedSpace.chartAt p : OpenPartialHomeomorph (HyperellipticAffine H) ℂ).symm.trans
          (ChartedSpace.chartAt q : OpenPartialHomeomorph (HyperellipticAffine H) ℂ) := by
    simpa [affineLiftChart] using
      (OpenPartialHomeomorph.lift_openEmbedding_trans
        (e := (ChartedSpace.chartAt p : OpenPartialHomeomorph (HyperellipticAffine H) ℂ))
        (e' := (ChartedSpace.chartAt q : OpenPartialHomeomorph (HyperellipticAffine H) ℂ))
        (hf := OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H)))
  rw [hEq]
  exact HyperellipticAffine.affineChartAt_compat (H := H) p q

/-- Infinity chart followed by the chosen lifted affine chart. -/
theorem infinityChart_compat_affineLift (p : HyperellipticAffine H) :
    ContDiffOn ℂ ω
      (((infinityChart H h).symm.trans (affineLiftChart (H := H) (h := h) p)) : ℂ → ℂ)
      ((infinityChart H h).symm.trans (affineLiftChart (H := H) (h := h) p)).source := by
  by_cases hpY : p ∈ HyperellipticAffine.smoothLocusY H
  · have hchart :
        (ChartedSpace.chartAt p : OpenPartialHomeomorph (HyperellipticAffine H) ℂ) =
          HyperellipticAffine.affineChartProjX (H := H) p hpY := by
        change HyperellipticAffine.affineChartAt (H := H) p =
          HyperellipticAffine.affineChartProjX (H := H) p hpY
        simp [HyperellipticAffine.affineChartAt, hpY]
    rw [affineLiftChart, hchart]
    exact infinityChart_compat_affineLiftProjX (H := H) (h := h) p hpY
  · have hpX : p ∈ HyperellipticAffine.smoothLocusX H :=
      HyperellipticAffine.mem_smoothLocusX_of_y_eq_zero H (by simpa [HyperellipticAffine.smoothLocusY] using hpY)
    have hchart :
        (ChartedSpace.chartAt p : OpenPartialHomeomorph (HyperellipticAffine H) ℂ) =
          HyperellipticAffine.affineChartProjY (H := H) p hpX := by
        change HyperellipticAffine.affineChartAt (H := H) p =
          HyperellipticAffine.affineChartProjY (H := H) p hpX
        simp [HyperellipticAffine.affineChartAt, hpY, hpX]
    rw [affineLiftChart, hchart]
    exact infinityChart_compat_affineLiftProjY (H := H) (h := h) p hpX

/-- Chosen lifted affine chart followed by the infinity chart. -/
theorem affineLift_compat_infinityChart (p : HyperellipticAffine H) :
    ContDiffOn ℂ ω
      (((affineLiftChart (H := H) (h := h) p).symm.trans (infinityChart H h)) : ℂ → ℂ)
      ((affineLiftChart (H := H) (h := h) p).symm.trans (infinityChart H h)).source := by
  by_cases hpY : p ∈ HyperellipticAffine.smoothLocusY H
  · have hchart :
        (ChartedSpace.chartAt p : OpenPartialHomeomorph (HyperellipticAffine H) ℂ) =
          HyperellipticAffine.affineChartProjX (H := H) p hpY := by
        change HyperellipticAffine.affineChartAt (H := H) p =
          HyperellipticAffine.affineChartProjX (H := H) p hpY
        simp [HyperellipticAffine.affineChartAt, hpY]
    rw [affineLiftChart, hchart]
    exact affineLiftProjX_compat_infinityChart (H := H) (h := h) p hpY
  · have hpX : p ∈ HyperellipticAffine.smoothLocusX H :=
      HyperellipticAffine.mem_smoothLocusX_of_y_eq_zero H (by simpa [HyperellipticAffine.smoothLocusY] using hpY)
    have hchart :
        (ChartedSpace.chartAt p : OpenPartialHomeomorph (HyperellipticAffine H) ℂ) =
          HyperellipticAffine.affineChartProjY (H := H) p hpX := by
        change HyperellipticAffine.affineChartAt (H := H) p =
          HyperellipticAffine.affineChartProjY (H := H) p hpX
        simp [HyperellipticAffine.affineChartAt, hpY, hpX]
    rw [affineLiftChart, hchart]
    exact affineLiftProjY_compat_infinityChart (H := H) (h := h) p hpX

/-- **Charted-space instance on `HyperellipticOdd H h`.** Combines:

* affine chart via `affineChartProjX` for points `(x, y)` with `y ≠ 0`
  pulled back through `OnePoint.openEmbedding_coe`;
* affine chart via `affineChartProjY` for points `(x, y)` with `y = 0`
  (necessarily `f'(x) ≠ 0`);
* `infinityChart` for the single added point `OnePoint.infty`. -/
noncomputable instance instChartedSpace (H : HyperellipticData) (h : Odd H.f.natDegree) :
    ChartedSpace ℂ (HyperellipticOdd H h)
    where
  atlas := Set.range (chartAt (H := H) (h := h))
  chartAt := chartAt (H := H) (h := h)
  mem_chart_source p := by
    induction p using OnePoint.rec with
    | infty =>
        simpa using infinityChart_mem_source H h
    | coe q =>
        simpa using mem_affineLiftChart_source (H := H) (h := h) q
  chart_mem_atlas p := ⟨p, rfl⟩

/-- **Manifold instance on `HyperellipticOdd H h`.** Verifies that all
pairwise chart transitions are analytic (`ContDiffOn ω`):

* `affineProjX × affineProjY` (Phase OA1, overlap where both `y ≠ 0`
  and `f'(x) ≠ 0`) — analytic by the implicit function theorem;
* `affine × infinity` (Phase OA2 compat lemma) — analytic via
  `t ↦ x(t) = 1 / (lc(f) · t²) (1 + O(t))`. -/
noncomputable instance instIsManifold (H : HyperellipticData) (h : Odd H.f.natDegree) :
    IsManifold 𝓘(ℂ, ℂ) ω (HyperellipticOdd H h)
    := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  rcases he with ⟨x, rfl⟩
  rcases he' with ⟨y, rfl⟩
  induction x using OnePoint.rec generalizing y with
  | infty =>
      induction y using OnePoint.rec with
      | infty =>
          have hself :
              ContDiffOn ℂ ω
                (((infinityChart H h).symm.trans (infinityChart H h)) : ℂ → ℂ)
                ((infinityChart H h).symm.trans (infinityChart H h)).source := by
            exact
              (contMDiffOn_of_mem_contDiffGroupoid (I := 𝓘(ℂ, ℂ)) (n := ω)
                (symm_trans_mem_contDiffGroupoid (I := 𝓘(ℂ, ℂ)) (n := ω)
                  (infinityChart H h))).contDiffOn
          simpa only [chartAt_infty, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
            Set.range_id, Set.preimage_id, id_eq, Set.inter_univ, Set.univ_inter] using
            hself
      | coe q =>
          simpa only [chartAt_infty, chartAt_coe, modelWithCornersSelf_coe,
            modelWithCornersSelf_coe_symm, Set.range_id, Set.inter_univ, Set.univ_inter,
            Set.preimage_id, id_eq] using
            infinityChart_compat_affineLift (H := H) (h := h) q
  | coe p =>
      induction y using OnePoint.rec with
      | infty =>
          simpa only [chartAt_infty, chartAt_coe, modelWithCornersSelf_coe,
            modelWithCornersSelf_coe_symm, Set.range_id, Set.inter_univ, Set.univ_inter,
            Set.preimage_id, id_eq] using
            affineLift_compat_infinityChart (H := H) (h := h) p
      | coe q =>
          simpa only [chartAt_coe, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
            Set.range_id, Set.inter_univ, Set.univ_inter, Set.preimage_id, id_eq] using
            affineLiftChart_compat (H := H) (h := h) p q

end Jacobians.ProjectiveCurve.HyperellipticOdd
