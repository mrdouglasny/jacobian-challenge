import Jacobians.RiemannSurface.HomotopyInvarianceDevelop
import Jacobians.RiemannSurface.Homology
import Jacobians.RiemannSurface.DevelopingBridge
import Jacobians.RiemannSurface.LoopIntegral
import Jacobians.Axioms.PeriodLattice
import Jacobians.Axioms.PeriodCycleBasis

/-!
# Loop integrals as homomorphisms

This file turns the homotopy-invariant developing value into a homomorphism
on the fundamental group, then descends it to the abelianized first homology.
-/

noncomputable section

namespace Jacobians.RiemannSurface

open scoped Manifold Topology
open scoped ContDiff

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-- The developing value of a based loop, descended to homotopy classes. -/
noncomputable def loopDevValQuotient (x₀ : X) (form : HolomorphicOneForm X)
    (γ : Path.Homotopic.Quotient x₀ x₀) : ℂ :=
  Quotient.liftOn γ
    (fun γp : Path x₀ x₀ =>
      developingValue x₀ form ((γp : Path x₀ x₀) : C(unitInterval, X)))
    (by
      intro γ₁ γ₂ hγ
      rcases hγ with ⟨H⟩
      exact developingValue_homotopy_invariance x₀ form H)

@[simp] theorem loopDevValQuotient_mk (x₀ : X) (form : HolomorphicOneForm X)
    (γ : Path x₀ x₀) :
    loopDevValQuotient x₀ form (Path.Homotopic.Quotient.mk γ) =
      developingValue x₀ form ((γ : Path x₀ x₀) : C(unitInterval, X)) :=
  rfl

/-- The developing value as a homomorphism on the fundamental group.

`FundamentalGroup` uses `End` multiplication, so `γ * δ` is represented by
the categorical composite `δ ≫ γ`; the target is abelian, so the order reversal
is harmless. -/
noncomputable def loopDevValHom (x₀ : X) (form : HolomorphicOneForm X) :
    FundamentalGroup X x₀ →* Multiplicative ℂ where
  toFun γ :=
    Multiplicative.ofAdd (loopDevValQuotient x₀ form (FundamentalGroup.toPath γ))
  map_one' := by
    change Multiplicative.ofAdd
        (loopDevValQuotient x₀ form (Path.Homotopic.Quotient.refl x₀)) = 1
    rw [Path.Homotopic.Quotient.refl, loopDevValQuotient_mk, devVal_refl]
    rfl
  map_mul' γ δ := by
    change Multiplicative.ofAdd
        (loopDevValQuotient x₀ form (FundamentalGroup.toPath (γ * δ))) =
      Multiplicative.ofAdd
        (loopDevValQuotient x₀ form (FundamentalGroup.toPath γ)) *
        Multiplicative.ofAdd
          (loopDevValQuotient x₀ form (FundamentalGroup.toPath δ))
    induction γ using Path.Homotopic.Quotient.ind with
    | mk γp =>
      induction δ using Path.Homotopic.Quotient.ind with
      | mk δp =>
        change Multiplicative.ofAdd
            (loopDevValQuotient x₀ form
              (Path.Homotopic.Quotient.mk (δp.trans γp))) =
          Multiplicative.ofAdd
            (loopDevValQuotient x₀ form (Path.Homotopic.Quotient.mk γp)) *
            Multiplicative.ofAdd
              (loopDevValQuotient x₀ form (Path.Homotopic.Quotient.mk δp))
        rw [loopDevValQuotient_mk, loopDevValQuotient_mk,
          loopDevValQuotient_mk, devVal_trans]
        simp [add_comm]

/-- The developing value as an additive homomorphism on `H1`. -/
noncomputable def loopDevValH1Hom (x₀ : X) (form : HolomorphicOneForm X) :
    H1 X x₀ →+ ℂ :=
  MonoidHom.toAdditiveLeft (Abelianization.lift (loopDevValHom x₀ form))

@[simp] theorem loopDevValH1Hom_of (x₀ : X) (form : HolomorphicOneForm X)
    (γ : FundamentalGroup X x₀) :
    loopDevValH1Hom x₀ form (Additive.ofMul (Abelianization.of γ)) =
      (loopDevValHom x₀ form γ).toAdd :=
  rfl

/-- Compatibility with the canonical arc integral for any analytic loop. -/
@[simp] theorem loopDevValH1Hom_loopToHomology
    (x₀ : X) (form : HolomorphicOneForm X) (loop : AnalyticLoop X x₀) :
    loopDevValH1Hom x₀ form (Jacobians.Axioms.loopToHomology loop) =
      canonicalArcIntegral loop.arc form := by
  rw [← developingValue_eq_canonicalArcIntegral x₀ form loop.arc]
  rfl

/-- Compatibility for any indexed family of analytic loops, such as the loops
in an analytic cycle basis. -/
theorem loopDevValH1Hom_loopToHomology_apply {ι : Type*}
    (x₀ : X) (form : HolomorphicOneForm X) (loops : ι → AnalyticLoop X x₀)
    (i : ι) :
    loopDevValH1Hom x₀ form (Jacobians.Axioms.loopToHomology (loops i)) =
      canonicalArcIntegral (loops i).arc form :=
  loopDevValH1Hom_loopToHomology x₀ form (loops i)

/-- The homology-level developing-value functional agrees with the
cycle-basis period pairing used to define `loopIntegralToH1`. -/
theorem loopDevValH1Hom_eq_loopIntegralToH1_apply {X : Type*}
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (x₀ : X) (form : HolomorphicOneForm X) (h : H1 X x₀) :
    loopDevValH1Hom x₀ form h = (loopIntegralToH1 x₀ h) form := by
  classical
  let cb := Classical.choice (Jacobians.Axioms.AX_PeriodCycleBasis x₀)
  let F : H1 X x₀ →ₗ[ℤ] ℂ := (loopDevValH1Hom x₀ form).toIntLinearMap
  let G : H1 X x₀ →ₗ[ℤ] ℂ :=
    { toFun := fun h => (loopIntegralToH1 x₀ h) form
      map_add' := by
        intro h₁ h₂
        simp
      map_smul' := by
        intro n h
        simp }
  have hFG : F = G := by
    refine cb.isBasis.ext (fun i => ?_)
    rw [show cb.isBasis i = Jacobians.Axioms.loopToHomology (cb.loops i) from
      cb.loops_to_basis i]
    change loopDevValH1Hom x₀ form (Jacobians.Axioms.loopToHomology (cb.loops i)) =
      (loopIntegralToH1 x₀ (Jacobians.Axioms.loopToHomology (cb.loops i))) form
    rw [loopDevValH1Hom_loopToHomology]
    have hloop :=
      congrArg (fun L : HolomorphicOneForm X →ₗ[ℂ] ℂ => L form)
        (loopIntegralToH1_loop x₀ i)
    simpa [cb, arcPeriodFunctional] using hloop.symm
  exact LinearMap.congr_fun hFG h

/-- The coordinate vector of the developing-value homology functional lies in
the period lattice written in any holomorphic-one-form basis. -/
theorem loopDevValH1Hom_mem_periodLatticeInBasis {X : Type*}
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (x₀ : X) (b : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X))
    (h : H1 X x₀) :
    (fun i => loopDevValH1Hom x₀ (b i) h) ∈
      Jacobians.Axioms.periodLatticeInBasis X x₀ b := by
  refine ⟨h, ?_⟩
  ext i
  calc
    Jacobians.Axioms.periodMapInBasis X x₀ b h i =
        (loopIntegralToH1 x₀ h) (b i) := by
      simp [Jacobians.Axioms.periodMapInBasis, periodMap, LinearMap.comp_apply,
        b.dualBasis_equivFun]
    _ = loopDevValH1Hom x₀ (b i) h :=
      (loopDevValH1Hom_eq_loopIntegralToH1_apply x₀ (b i) h).symm

/-- The period vector of an analytic loop lies in the period lattice. -/
theorem loop_canonicalArcIntegral_mem_periodLatticeInBasis {X : Type*}
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (x₀ : X) (b : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X))
    (loop : AnalyticLoop X x₀) :
    (fun i => canonicalArcIntegral loop.arc (b i)) ∈
      Jacobians.Axioms.periodLatticeInBasis X x₀ b := by
  have hmem :=
    loopDevValH1Hom_mem_periodLatticeInBasis x₀ b
      (Jacobians.Axioms.loopToHomology loop)
  convert hmem using 1
  ext i
  exact (loopDevValH1Hom_loopToHomology x₀ (b i) loop).symm

end Jacobians.RiemannSurface
