import Jacobians.ProjectiveCurve.Elliptic.Periods
import Jacobians.Axioms.AbelJacobiMap

namespace Jacobians.ProjectiveCurve

open scoped Manifold Topology
open scoped ContDiff
open intervalIntegral MeasureTheory
open Jacobians.RiemannSurface
open Jacobians.AbelianVariety
open Jacobians.Axioms

variable {ω₁ ω₂ : ℂ} {h : LinearIndependent ℝ ![ω₁, ω₂]}

namespace EllipticOfCurveInj

/-- The invariant differential `dz` has coefficient `1` at every chart center. -/
theorem ellipticDz_coeff_chart_center (P : Elliptic ω₁ ω₂ h) :
    (ellipticDz ω₁ ω₂ h).coeff P ((extChartAt 𝓘(ℂ, ℂ) P) P) = 1 := by
  change Set.indicator _ (fun _ => (1 : ℂ)) _ = 1
  exact Set.indicator_of_mem (mem_extChartAt_target (I := 𝓘(ℂ, ℂ)) P) _

/-- Along a bridge path on an elliptic curve, the canonical `dz` integrand is
the derivative of any differentiable universal-cover lift supplied by
`ComplexTorus.exists_lift_of_chart_path`. -/
theorem bridgePath_canonicalIntegrand_ellipticDz_eq_lift_deriv
    (P₀ Q : Elliptic ω₁ ω₂ h) (liftBP : ℝ → ℂ)
    (hlift_deriv : ∀ t : ℝ,
      deriv liftBP t =
        deriv ((extChartAt 𝓘(ℂ, ℂ)
          (Jacobians.Bridge.bridgePath (X := Elliptic ω₁ ω₂ h) P₀ Q t)) ∘
            Jacobians.Bridge.bridgePath (X := Elliptic ω₁ ω₂ h) P₀ Q) t)
    (t : ℝ) :
    canonicalIntegrand (Jacobians.Bridge.bridgePathArc (X := Elliptic ω₁ ω₂ h) P₀ Q)
        (ellipticDz ω₁ ω₂ h) t =
      deriv liftBP t := by
  rw [canonicalIntegrand]
  rw [ellipticDz_coeff_chart_center]
  rw [one_mul]
  rw [hlift_deriv]
  rfl

/-- The canonical `dz` integrand along a bridge path is interval-integrable. -/
theorem bridgePath_canonicalIntegrand_ellipticDz_intervalIntegrable
    (P₀ Q : Elliptic ω₁ ω₂ h) :
    IntervalIntegrable
      (canonicalIntegrand
        (Jacobians.Bridge.bridgePathArc (X := Elliptic ω₁ ω₂ h) P₀ Q)
        (ellipticDz ω₁ ω₂ h)) MeasureTheory.volume 0 1 := by
  let f : ℝ → ℂ := fun t =>
    (Jacobians.Bridge.bridgeForm (ellipticDz ω₁ ω₂ h)).toFun
      (Jacobians.Bridge.bridgePath (X := Elliptic ω₁ ω₂ h) P₀ Q t)
      (Jacobians.Vendor.Kirov.pathSpeed
        (Jacobians.Bridge.bridgePath (X := Elliptic ω₁ ω₂ h) P₀ Q) t)
  have hf : IntervalIntegrable f MeasureTheory.volume 0 1 :=
    Jacobians.Bridge.bridgePath_lineIntegrable
      (X := Elliptic ω₁ ω₂ h) P₀ Q (ellipticDz ω₁ ω₂ h)
  refine hf.congr ?_
  intro t _ht
  exact Jacobians.Bridge.bridge_kirov_integrand_eq_canonicalIntegrand
    (X := Elliptic ω₁ ω₂ h) P₀ Q (ellipticDz ω₁ ω₂ h) t

/-- Lift-based computation of the bridge integral of `dz`: it is the endpoint
difference of the universal-cover lift of the bridge path. -/
theorem bridgePath_canonicalArcIntegral_ellipticDz_eq_lift_sub
    (P₀ Q : Elliptic ω₁ ω₂ h) :
    ∃ liftBP : ℝ → ℂ,
      (∀ t : ℝ,
        (QuotientAddGroup.mk' (ellipticLattice ω₁ ω₂ h).toAddSubgroup
          (liftBP t) : Elliptic ω₁ ω₂ h) =
          Jacobians.Bridge.bridgePath (X := Elliptic ω₁ ω₂ h) P₀ Q t) ∧
      (∀ t : ℝ, DifferentiableAt ℝ liftBP t) ∧
      canonicalArcIntegral
          (Jacobians.Bridge.bridgePathArc (X := Elliptic ω₁ ω₂ h) P₀ Q)
          (ellipticDz ω₁ ω₂ h) =
        liftBP 1 - liftBP 0 := by
  rcases ComplexTorus.exists_lift_of_chart_path
      (L := ellipticLattice ω₁ ω₂ h)
      (g := Jacobians.Bridge.bridgePath (X := Elliptic ω₁ ω₂ h) P₀ Q)
      (Jacobians.Bridge.bridgePath_continuous (X := Elliptic ω₁ ω₂ h) P₀ Q)
      (Jacobians.Bridge.bridgePath_chart_differentiable (X := Elliptic ω₁ ω₂ h) P₀ Q) with
    ⟨liftBP, hlift_mk, hlift_diff, hlift_deriv⟩
  refine ⟨liftBP, hlift_mk, hlift_diff, ?_⟩
  have hderiv_eq :
      (fun t : ℝ =>
        canonicalIntegrand
          (Jacobians.Bridge.bridgePathArc (X := Elliptic ω₁ ω₂ h) P₀ Q)
          (ellipticDz ω₁ ω₂ h) t) =
        deriv liftBP := by
    funext t
    exact bridgePath_canonicalIntegrand_ellipticDz_eq_lift_deriv
      (P₀ := P₀) (Q := Q) liftBP hlift_deriv t
  have hint_deriv : IntervalIntegrable (deriv liftBP) MeasureTheory.volume 0 1 := by
    rw [← hderiv_eq]
    exact bridgePath_canonicalIntegrand_ellipticDz_intervalIntegrable (P₀ := P₀) (Q := Q)
  unfold canonicalArcIntegral
  rw [hderiv_eq]
  exact intervalIntegral.integral_deriv_eq_sub
    (a := (0 : ℝ)) (b := 1) (f := liftBP)
    (fun x _hx => hlift_diff x) hint_deriv

/-- Along an analytic loop on an elliptic curve, the period of the invariant
form `dz` belongs to the defining elliptic lattice. -/
theorem analyticLoop_canonicalArcIntegral_ellipticDz_mem_lattice
    {x0 : Elliptic ω₁ ω₂ h} (g : AnalyticLoop (Elliptic ω₁ ω₂ h) x0) :
    canonicalArcIntegral g.arc (ellipticDz ω₁ ω₂ h) ∈ ellipticLattice ω₁ ω₂ h := by
  let integrand : ℝ → ℂ := canonicalIntegrand g.arc (ellipticDz ω₁ ω₂ h)
  rcases ComplexTorus.exists_lift_of_continuous_path
      (L := ellipticLattice ω₁ ω₂ h)
      (g := g.arc.extend) g.arc.continuous' with
    ⟨liftLoop, hlift_cont, hlift_mk, hlift_point⟩
  by_cases hint : IntervalIntegrable integrand MeasureTheory.volume 0 1
  · have hperiod_eq :
        canonicalArcIntegral g.arc (ellipticDz ω₁ ω₂ h) = liftLoop 1 - liftLoop 0 := by
      have hFTC :
          ∫ t in (0 : ℝ)..1, integrand t = liftLoop 1 - liftLoop 0 := by
        refine MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le
          liftLoop integrand zero_le_one
          (s := (g.arc.partition : Set ℝ))
          g.arc.partition.countable_toSet hlift_cont.continuousOn ?_ hint
        intro t ht
        have ht01 : t ∈ Set.Ioo (0 : ℝ) 1 := ht.1
        have ht_not_partition : t ∉ (g.arc.partition : Set ℝ) := ht.2
        have hchart :
            DifferentiableAt ℝ
              ((extChartAt 𝓘(ℂ, ℂ) (g.arc.extend t)) ∘ g.arc.extend) t := by
          simpa using (g.arc.is_analytic t ht01 ht_not_partition).differentiableAt
        have hpoint := hlift_point t hchart
        have hintegrand : integrand t = deriv liftLoop t := by
          change canonicalIntegrand g.arc (ellipticDz ω₁ ω₂ h) t = deriv liftLoop t
          rw [canonicalIntegrand]
          rw [ellipticDz_coeff_chart_center]
          rw [one_mul]
          exact hpoint.2.symm
        exact hpoint.1.hasDerivAt.congr_deriv hintegrand.symm
      simpa [canonicalArcIntegral, integrand] using hFTC
    have hmk_eq :
        (QuotientAddGroup.mk' (ellipticLattice ω₁ ω₂ h).toAddSubgroup (liftLoop 1) :
            ComplexTorus ℂ (ellipticLattice ω₁ ω₂ h)) =
          QuotientAddGroup.mk' (ellipticLattice ω₁ ω₂ h).toAddSubgroup (liftLoop 0) := by
      have hloop_eq :
          (g.arc.extend 1 : ComplexTorus ℂ (ellipticLattice ω₁ ω₂ h)) =
            (g.arc.extend 0 : ComplexTorus ℂ (ellipticLattice ω₁ ω₂ h)) := by
        change (g.arc.extend 1 : Elliptic ω₁ ω₂ h) = g.arc.extend 0
        exact g.end_eq.trans g.start_eq.symm
      exact (hlift_mk 1).trans (hloop_eq.trans (hlift_mk 0).symm)
    have hsub_mem :
        liftLoop 1 - liftLoop 0 ∈ (ellipticLattice ω₁ ω₂ h).toAddSubgroup := by
      exact (QuotientAddGroup.eq_iff_sub_mem (N := (ellipticLattice ω₁ ω₂ h).toAddSubgroup)).mp
        (by simpa [Elliptic, QuotientAddGroup.mk'_apply] using hmk_eq)
    rw [hperiod_eq]
    simpa using hsub_mem
  · have hzero : canonicalArcIntegral g.arc (ellipticDz ω₁ ω₂ h) = 0 := by
      simpa [canonicalArcIntegral, integrand] using
        (intervalIntegral.integral_undef (a := (0 : ℝ)) (b := 1)
          (f := integrand) (μ := MeasureTheory.volume) hint)
    rw [hzero]
    exact Submodule.zero_mem _

end EllipticOfCurveInj

end Jacobians.ProjectiveCurve
