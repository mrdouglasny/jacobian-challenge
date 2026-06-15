/-
# The hyperelliptic involution on `HyperellipticOdd`

This file defines the hyperelliptic involution `σ(x, y) = (x, −y)` on the odd-degree
projective curve `HyperellipticOdd H h`.
-/
import Jacobians.ProjectiveCurve.Hyperelliptic.Basic
import Jacobians.ProjectiveCurve.Hyperelliptic.OddAtlas
import Jacobians.ProjectiveCurve.Hyperelliptic.Involution
import Mathlib.Geometry.Manifold.ContMDiff.Basic

open scoped Manifold ContDiff Topology
open Jacobians.ProjectiveCurve
open Jacobians.ProjectiveCurve.HyperellipticAffine
open Jacobians.ProjectiveCurve.HyperellipticOdd

variable {H : HyperellipticData} {h : Odd H.f.natDegree}

/-- **Hyperelliptic involution** `σ : (x, y) ↦ (x, -y)` on the smooth
model of a hyperelliptic curve. -/
noncomputable def hyperellipticInvolution
    (H : HyperellipticData) (h : Odd H.f.natDegree) :
    HyperellipticOdd H h → HyperellipticOdd H h :=
  -- On the affine chart: send `⟨(x, y), hxy⟩` to `⟨(x, -y), neg_pow ▸ hxy⟩`.
  -- At infinity (single point in the odd-degree case): identity.
  fun p =>
    p.elim (OnePoint.infty : HyperellipticOdd H h)
      (fun q => (((q.invol : HyperellipticAffine H) :
        OnePoint (HyperellipticAffine H)) : HyperellipticOdd H h))

/-- The hyperelliptic involution is an order-2 map: `σ ∘ σ = id`. -/
theorem hyperellipticInvolution_involutive
    (H : HyperellipticData) (h : Odd H.f.natDegree) :
    Function.Involutive (hyperellipticInvolution H h) := by
  intro p
  induction p using OnePoint.rec with
  | infty =>
      simp [hyperellipticInvolution]
  | coe q =>
      simp [hyperellipticInvolution, HyperellipticAffine.invol_invol]

lemma hyperellipticInvolution_infinityChart (q : HyperellipticAffine H) :
    (infinityChart H h) (coe (q.invol) : HyperellipticOdd H h) =
      - (infinityChart H h) (coe q : HyperellipticOdd H h) := by
  change infinityForward H h (coe (q.invol)) = - infinityForward H h (coe q)
  change (q.invol).val.2 / (q.invol).val.1 ^ (H.genus + 1) =
    - (q.val.2 / q.val.1 ^ (H.genus + 1))
  simp only [HyperellipticAffine.invol_val]
  ring

lemma hyperellipticInvolution_extChartAt_infty (z : ℂ)
    (hz_target : z ∈ (InfinityInverse.tLocalHomeomorph H).target) :
    (extChartAt (M := HyperellipticOdd H h) 𝓘(ℂ, ℂ) (infty : HyperellipticOdd H h))
      (hyperellipticInvolution H h
        ((extChartAt (M := HyperellipticOdd H h) 𝓘(ℂ, ℂ) (infty : HyperellipticOdd H h)).symm z))
      = -z := by
  change (infinityChart H h) (hyperellipticInvolution H h (infinityBackward H h z)) = -z
  by_cases hz : z = 0
  · rw [hz, neg_zero]
    change (infinityChart H h) (hyperellipticInvolution H h (infinityBackward H h 0)) = 0
    have h0 : infinityBackward H h 0 = (infty : HyperellipticOdd H h) := by
      unfold infinityBackward; rw [if_pos rfl]; rfl
    rw [h0]
    change infinityForward H h infty = 0
    rfl
  · have hb : infinityBackward H h z = coe (InfinityInverse.infinityInverseMap H h z) := by
      unfold infinityBackward; rw [if_neg hz]
    rw [hb]
    change (infinityChart H h) (coe (InfinityInverse.infinityInverseMap H h z).invol) = -z
    rw [hyperellipticInvolution_infinityChart]
    have hz_fwd :
        (infinityChart H h) (coe (InfinityInverse.infinityInverseMap H h z) :
          HyperellipticOdd H h) = z := by
      change infinityForward H h (coe (InfinityInverse.infinityInverseMap H h z)) = z
      exact infinityForward_infinityInverseMap_eq_self z hz_target hz
    rw [hz_fwd]

lemma continuous_hyperellipticInvolution : Continuous (hyperellipticInvolution H h) := by
  let hHomeo : Homeomorph (HyperellipticAffine H) (HyperellipticAffine H) :=
    { toFun := HyperellipticAffine.invol
      invFun := HyperellipticAffine.invol
      left_inv := HyperellipticAffine.invol_invol
      right_inv := HyperellipticAffine.invol_invol
      continuous_toFun := HyperellipticAffine.continuous_invol
      continuous_invFun := HyperellipticAffine.continuous_invol }
  have hCont := (Homeomorph.onePointCongr hHomeo).continuous
  convert hCont using 1
  ext x
  cases x <;> rfl

/-- The hyperelliptic involution is smooth (hence in particular
`ContMDiff` for the `ω` smoothness level Buzzard's challenge uses). -/
theorem hyperellipticInvolution_contMDiff
    (H : HyperellipticData) (h : Odd H.f.natDegree) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (hyperellipticInvolution H h) := by
  intro p
  induction p using OnePoint.rec with
  | infty =>
    rw [contMDiffAt_iff]
    refine ⟨(continuous_hyperellipticInvolution).continuousAt, ?_⟩
    have h_inv_inf : hyperellipticInvolution H h OnePoint.infty = OnePoint.infty := rfl
    rw [h_inv_inf]
    have h_chart_inf :
        (extChartAt (M := HyperellipticOdd H h) 𝓘(ℂ, ℂ) OnePoint.infty) OnePoint.infty = 0 := by
      change infinityForward H h infty = 0
      rfl
    rw [h_chart_inf]
    have hEq :
        (fun z : ℂ => (extChartAt (M := HyperellipticOdd H h) 𝓘(ℂ, ℂ) OnePoint.infty)
            (hyperellipticInvolution H h
              ((extChartAt (M := HyperellipticOdd H h) 𝓘(ℂ, ℂ) OnePoint.infty).symm z)))
          =ᶠ[nhds 0]
        (fun z : ℂ => -z) := by
      have h_mem : (InfinityInverse.tLocalHomeomorph H).target ∈ nhds (0 : ℂ) := by
        exact (InfinityInverse.tLocalHomeomorph H).open_target.mem_nhds
          (InfinityInverse.tLocalHomeomorph_target_zero H)
      exact Filter.eventually_of_mem h_mem hyperellipticInvolution_extChartAt_infty
    refine ContDiffWithinAt.congr_of_eventuallyEq ?_ (hEq.filter_mono nhdsWithin_le_nhds) ?_
    · exact contDiff_neg.contDiffWithinAt
    · change (fun z : ℂ => (extChartAt (M := HyperellipticOdd H h) 𝓘(ℂ, ℂ) OnePoint.infty)
          (hyperellipticInvolution H h
            ((extChartAt (M := HyperellipticOdd H h) 𝓘(ℂ, ℂ) OnePoint.infty).symm z))) 0
        = (fun z : ℂ => -z) 0
      exact hEq.self_of_nhds
  | coe a =>
    let c := HyperellipticOdd.affineLiftChart (h := h) a
    let c' := HyperellipticOdd.affineLiftChart (h := h) (a.invol)
    have hc : c ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω (HyperellipticOdd H h) := by
      change chartAt ℂ (coe a : HyperellipticOdd H h) ∈ _
      exact IsManifold.chart_mem_maximalAtlas (coe a : HyperellipticOdd H h)
    have hc' : c' ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω (HyperellipticOdd H h) := by
      change chartAt ℂ (coe (a.invol) : HyperellipticOdd H h) ∈ _
      exact IsManifold.chart_mem_maximalAtlas (coe (a.invol) : HyperellipticOdd H h)
    have hx : (coe a : HyperellipticOdd H h) ∈ c.source := by
      exact mem_affineLiftChart_source a
    have hy : hyperellipticInvolution H h (coe a) ∈ c'.source := by
      change (coe (a.invol) : HyperellipticOdd H h) ∈ c'.source
      exact mem_affineLiftChart_source (a.invol)
    have h_invol_M := HyperellipticAffine.contMDiffAt_invol (H := H) a
    rw [contMDiffAt_iff] at h_invol_M
    have hCoord := h_invol_M.2
    have hFun :
      (c'.extend 𝓘(ℂ, ℂ)) ∘ hyperellipticInvolution H h ∘ (c.extend 𝓘(ℂ, ℂ)).symm =
      (extChartAt 𝓘(ℂ, ℂ) (a.invol)) ∘ HyperellipticAffine.invol ∘ (extChartAt 𝓘(ℂ, ℂ) a).symm := by
      funext z
      change c' (hyperellipticInvolution H h (c.symm z)) = _
      simp only [c, c', HyperellipticOdd.affineLiftChart,
        OpenPartialHomeomorph.lift_openEmbedding_symm,
        OpenPartialHomeomorph.lift_openEmbedding_toFun]
      exact (OnePoint.isOpenEmbedding_coe.injective (X := HyperellipticAffine H)).extend_apply _ _ _
    have hBase :
      (c.extend 𝓘(ℂ, ℂ)) (coe a) = (extChartAt 𝓘(ℂ, ℂ) a) a := by
      change c (coe a) = _
      simp only [c, HyperellipticOdd.affineLiftChart,
        OpenPartialHomeomorph.lift_openEmbedding_toFun]
      exact (OnePoint.isOpenEmbedding_coe.injective (X := HyperellipticAffine H)).extend_apply _ _ _
    change ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (hyperellipticInvolution H h) (coe a)
    rw [ContMDiffAt, contMDiffWithinAt_iff_of_mem_maximalAtlas hc hc' hx hy]
    refine ⟨(continuous_hyperellipticInvolution).continuousAt.continuousWithinAt, ?_⟩
    simpa only [Set.preimage_univ, Set.univ_inter, hFun, hBase] using hCoord
