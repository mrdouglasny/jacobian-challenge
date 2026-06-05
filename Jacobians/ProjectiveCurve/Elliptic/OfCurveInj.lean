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

/-- The unique coordinate index of the elliptic Jacobian ambient space. -/
noncomputable def ellipticCoordZero (ω₁ ω₂ : ℂ)
    (h : LinearIndependent ℝ ![ω₁, ω₂]) : Fin (genus (Elliptic ω₁ ω₂ h)) :=
  ⟨0, by rw [genus_Elliptic_eq_one ω₁ ω₂ h]; exact Nat.zero_lt_one⟩

/-- Multiplication by a fixed complex scalar, viewed as a `ℤ`-linear map. -/
def complexScaleIntLinear (c : ℂ) : ℂ →ₗ[ℤ] ℂ where
  toFun z := c * z
  map_add' z w := by rw [mul_add]
  map_smul' n z := by
    simp [mul_assoc, mul_comm]

/-- The zero coordinate of any elliptic period vector lies in the scalar
multiple of the defining elliptic lattice determined by the zero basis form. -/
theorem periodMapInBasis_ellipticCoordZero_mem_scaled_lattice
    (x0 : Elliptic ω₁ ω₂ h) (c : ℂ)
    (hb : jacobianBasis (Elliptic ω₁ ω₂ h) (ellipticCoordZero ω₁ ω₂ h) =
        c • ellipticDz ω₁ ω₂ h)
    (z : H1 (Elliptic ω₁ ω₂ h) x0) :
    (periodMapInBasis (Elliptic ω₁ ω₂ h) x0
        (jacobianBasis (Elliptic ω₁ ω₂ h)) z)
        (ellipticCoordZero ω₁ ω₂ h) ∈
      (ellipticLattice ω₁ ω₂ h).map (complexScaleIntLinear c) := by
  let i0 := ellipticCoordZero ω₁ ω₂ h
  let cb := Classical.choice (AX_AnalyticCycleBasis x0)
  let eval0 : (Fin (genus (Elliptic ω₁ ω₂ h)) → ℂ) →ₗ[ℤ] ℂ :=
    { toFun := fun v => v i0
      map_add' := by intro v w; rfl
      map_smul' := by intro n v; rfl }
  let F : H1 (Elliptic ω₁ ω₂ h) x0 →ₗ[ℤ] ℂ :=
    eval0.comp
      (periodMapInBasis (Elliptic ω₁ ω₂ h) x0
        (jacobianBasis (Elliptic ω₁ ω₂ h)))
  let S : Submodule ℤ ℂ :=
    (ellipticLattice ω₁ ω₂ h).map (complexScaleIntLinear c)
  have hbasis : ∀ i : Fin (2 * genus (Elliptic ω₁ ω₂ h)), F (cb.isBasis i) ∈ S := by
    intro i
    have hloop' :
        loopIntegralToH1 x0 (loopToHomology (cb.loops i)) =
          arcPeriodFunctional (cb.loops i).arc
            (fun form => AX_cycleBasisLoop_integrable x0 cb i form) := by
      simpa [cb] using loopIntegralToH1_loop (X := Elliptic ω₁ ω₂ h) x0 i
    have hcb : cb.isBasis i = loopToHomology (cb.loops i) := cb.loops_to_basis i
    have hF :
        F (cb.isBasis i) =
          c * canonicalArcIntegral (cb.loops i).arc (ellipticDz ω₁ ω₂ h) := by
      calc
        F (cb.isBasis i)
            = (periodMapInBasis (Elliptic ω₁ ω₂ h) x0
                (jacobianBasis (Elliptic ω₁ ω₂ h)) (cb.isBasis i)) i0 := rfl
        _ = (periodMap (Elliptic ω₁ ω₂ h) x0 (cb.isBasis i))
              (jacobianBasis (Elliptic ω₁ ω₂ h) i0) := by
            simp [periodMapInBasis, LinearMap.comp_apply,
              (jacobianBasis (Elliptic ω₁ ω₂ h)).dualBasis_equivFun]
        _ = (periodMap (Elliptic ω₁ ω₂ h) x0 (loopToHomology (cb.loops i)))
              (c • ellipticDz ω₁ ω₂ h) := by
            rw [hcb, hb]
        _ = (arcPeriodFunctional (cb.loops i).arc
              (fun form => AX_cycleBasisLoop_integrable x0 cb i form))
              (c • ellipticDz ω₁ ω₂ h) := by
            rw [periodMap, hloop']
        _ = c * canonicalArcIntegral (cb.loops i).arc (ellipticDz ω₁ ω₂ h) := by
            simp [arcPeriodFunctional]
    rw [hF]
    exact ⟨canonicalArcIntegral (cb.loops i).arc (ellipticDz ω₁ ω₂ h),
      analyticLoop_canonicalArcIntegral_ellipticDz_mem_lattice
        (ω₁ := ω₁) (ω₂ := ω₂) (h := h) (cb.loops i), rfl⟩
  have hzsum : z = ∑ i, (cb.isBasis.repr z i) • cb.isBasis i :=
    (cb.isBasis.sum_repr z).symm
  have hFz : F z ∈ S := by
    rw [hzsum]
    simp only [map_sum, map_zsmul]
    exact Submodule.sum_mem S fun i _ =>
      Submodule.smul_mem S (cb.isBasis.repr z i) (hbasis i)
  simpa [F, eval0, S, i0] using hFz

/-- The Abel-Jacobi map from an elliptic curve to its Jacobian is injective. -/
theorem elliptic_ofCurve_injective (P₀ : Elliptic ω₁ ω₂ h) :
    Function.Injective (ofCurveImpl (Elliptic ω₁ ω₂ h) P₀) := by
  intro P Q hPQ
  let i0 := ellipticCoordZero ω₁ ω₂ h
  obtain ⟨c, hbasis⟩ :=
    eq_smul_ellipticDz ω₁ ω₂ h (jacobianBasis (Elliptic ω₁ ω₂ h) i0)
  have hc : c ≠ 0 := by
    intro hc0
    have hb0 : jacobianBasis (Elliptic ω₁ ω₂ h) i0 = 0 := by
      simpa [hc0] using hbasis
    exact (jacobianBasis (Elliptic ω₁ ω₂ h)).ne_zero i0 hb0
  let L := periodLatticeInBasis (Elliptic ω₁ ω₂ h)
    (Classical.arbitrary (Elliptic ω₁ ω₂ h))
    (jacobianBasis (Elliptic ω₁ ω₂ h))
  let AP := ofCurveAmbient (Elliptic ω₁ ω₂ h) P₀ P
  let AQ := ofCurveAmbient (Elliptic ω₁ ω₂ h) P₀ Q
  let A0 := ofCurveAmbient (Elliptic ω₁ ω₂ h) P₀ P₀
  change ULift.up (QuotientAddGroup.mk' L.toAddSubgroup (AP - A0)) =
      ULift.up (QuotientAddGroup.mk' L.toAddSubgroup (AQ - A0)) at hPQ
  have hq : QuotientAddGroup.mk' L.toAddSubgroup (AP - A0) =
      QuotientAddGroup.mk' L.toAddSubgroup (AQ - A0) := ULift.up.inj hPQ
  have hdiff_mem0 : ((AP - A0) - (AQ - A0)) ∈ L.toAddSubgroup := by
    exact (QuotientAddGroup.eq_iff_sub_mem (N := L.toAddSubgroup)).mp
      (by simpa [QuotientAddGroup.mk'_apply] using hq)
  have hdiff_mem : ((AP - A0) - (AQ - A0)) ∈ L := by
    simpa using hdiff_mem0
  have hw_lattice : AP - AQ ∈ L := by
    convert hdiff_mem using 1
    ext i
    simp only [Pi.sub_apply]
    abel
  have hw_coord_scaled : (AP - AQ) i0 ∈
      (ellipticLattice ω₁ ω₂ h).map (complexScaleIntLinear c) := by
    have hw_lattice' : AP - AQ ∈
        periodLatticeInBasis (Elliptic ω₁ ω₂ h)
          (Classical.arbitrary (Elliptic ω₁ ω₂ h))
          (jacobianBasis (Elliptic ω₁ ω₂ h)) := by
      simpa [L] using hw_lattice
    rw [periodLatticeInBasis] at hw_lattice'
    rcases hw_lattice' with ⟨z, hz⟩
    rw [← hz]
    exact periodMapInBasis_ellipticCoordZero_mem_scaled_lattice
      (ω₁ := ω₁) (ω₂ := ω₂) (h := h)
      (Classical.arbitrary (Elliptic ω₁ ω₂ h)) c (by simpa [i0] using hbasis) z
  have hcoord_eq :
      (AP - AQ) i0 =
        c * (canonicalArcIntegral
              (Jacobians.Bridge.bridgePathArc (X := Elliptic ω₁ ω₂ h) P₀ P)
              (ellipticDz ω₁ ω₂ h) -
            canonicalArcIntegral
              (Jacobians.Bridge.bridgePathArc (X := Elliptic ω₁ ω₂ h) P₀ Q)
              (ellipticDz ω₁ ω₂ h)) := by
    calc
      (AP - AQ) i0
          = pathIntegralBasepointFunctional (Elliptic ω₁ ω₂ h) P₀ P
              (jacobianBasis (Elliptic ω₁ ω₂ h) i0) -
            pathIntegralBasepointFunctional (Elliptic ω₁ ω₂ h) P₀ Q
              (jacobianBasis (Elliptic ω₁ ω₂ h) i0) := by
          rfl
      _ = pathIntegralBasepointFunctional (Elliptic ω₁ ω₂ h) P₀ P
              (c • ellipticDz ω₁ ω₂ h) -
            pathIntegralBasepointFunctional (Elliptic ω₁ ω₂ h) P₀ Q
              (c • ellipticDz ω₁ ω₂ h) := by
          rw [hbasis]
      _ = c * canonicalArcIntegral
              (Jacobians.Bridge.bridgePathArc (X := Elliptic ω₁ ω₂ h) P₀ P)
              (ellipticDz ω₁ ω₂ h) -
            c * canonicalArcIntegral
              (Jacobians.Bridge.bridgePathArc (X := Elliptic ω₁ ω₂ h) P₀ Q)
              (ellipticDz ω₁ ω₂ h) := by
          simp [pathIntegralBasepointFunctional]
      _ = c * (canonicalArcIntegral
              (Jacobians.Bridge.bridgePathArc (X := Elliptic ω₁ ω₂ h) P₀ P)
              (ellipticDz ω₁ ω₂ h) -
            canonicalArcIntegral
              (Jacobians.Bridge.bridgePathArc (X := Elliptic ω₁ ω₂ h) P₀ Q)
              (ellipticDz ω₁ ω₂ h)) := by
          ring
  rcases bridgePath_canonicalArcIntegral_ellipticDz_eq_lift_sub
      (ω₁ := ω₁) (ω₂ := ω₂) (h := h) P₀ P with
    ⟨liftP, hliftP_mk, _hliftP_diff, hIntP⟩
  rcases bridgePath_canonicalArcIntegral_ellipticDz_eq_lift_sub
      (ω₁ := ω₁) (ω₂ := ω₂) (h := h) P₀ Q with
    ⟨liftQ, hliftQ_mk, _hliftQ_diff, hIntQ⟩
  let Λ := ellipticLattice ω₁ ω₂ h
  let Δ : ℂ := (liftP 1 - liftP 0) - (liftQ 1 - liftQ 0)
  have hcΔ_mem_scaled : c * Δ ∈ Λ.map (complexScaleIntLinear c) := by
    rw [hcoord_eq, hIntP, hIntQ] at hw_coord_scaled
    simpa [Λ, Δ] using hw_coord_scaled
  have hΔ_mem : Δ ∈ Λ := by
    rcases hcΔ_mem_scaled with ⟨y, hyΛ, hy_eq⟩
    have hy_eq' : c * y = c * Δ := by
      simpa [complexScaleIntLinear] using hy_eq
    have hy : y = Δ := mul_left_cancel₀ hc hy_eq'
    simpa [Λ, hy.symm] using hyΛ
  have hzero_mk :
      (QuotientAddGroup.mk' Λ.toAddSubgroup (liftP 0) : Elliptic ω₁ ω₂ h) =
        QuotientAddGroup.mk' Λ.toAddSubgroup (liftQ 0) := by
    rw [hliftP_mk 0, hliftQ_mk 0]
    rw [Jacobians.Bridge.bridgePath_at_zero, Jacobians.Bridge.bridgePath_at_zero]
  have hzero_mem : liftP 0 - liftQ 0 ∈ Λ := by
    have hzero_mem0 : liftP 0 - liftQ 0 ∈ Λ.toAddSubgroup := by
      exact (QuotientAddGroup.eq_iff_sub_mem (N := Λ.toAddSubgroup)).mp
        (by simpa [Elliptic, QuotientAddGroup.mk'_apply] using hzero_mk)
    simpa [Λ] using hzero_mem0
  have hone_mem : liftP 1 - liftQ 1 ∈ Λ := by
    have hadd : Δ + (liftP 0 - liftQ 0) ∈ Λ :=
      Submodule.add_mem Λ hΔ_mem hzero_mem
    convert hadd using 1
    simp [Δ]
    ring
  have hone_mk :
      (QuotientAddGroup.mk' Λ.toAddSubgroup (liftP 1) : Elliptic ω₁ ω₂ h) =
        QuotientAddGroup.mk' Λ.toAddSubgroup (liftQ 1) := by
    exact (QuotientAddGroup.eq_iff_sub_mem (N := Λ.toAddSubgroup)).mpr
      (by simpa [Λ] using hone_mem)
  have hP_end :
      (QuotientAddGroup.mk' Λ.toAddSubgroup (liftP 1) : Elliptic ω₁ ω₂ h) = P := by
    rw [hliftP_mk 1]
    exact Jacobians.Bridge.bridgePath_at_one (X := Elliptic ω₁ ω₂ h) P₀ P
  have hQ_end :
      (QuotientAddGroup.mk' Λ.toAddSubgroup (liftQ 1) : Elliptic ω₁ ω₂ h) = Q := by
    rw [hliftQ_mk 1]
    exact Jacobians.Bridge.bridgePath_at_one (X := Elliptic ω₁ ω₂ h) P₀ Q
  exact hP_end.symm.trans (hone_mk.trans hQ_end)

end EllipticOfCurveInj

end Jacobians.ProjectiveCurve
