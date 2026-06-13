import Jacobians.RiemannSurface.HomotopyInvarianceDevelop
import Jacobians.RiemannSurface.Homology
import Jacobians.RiemannSurface.DevelopingBridge
import Jacobians.RiemannSurface.LoopIntegral
import Jacobians.Axioms.PeriodLattice
import Jacobians.Axioms.PeriodCycleBasis

/-!
# Loop integrals as homomorphisms — cycle-basis compatibility

The developing-value homomorphism on `H1` (`loopDevValH1Hom`) and the
form-linear developing period map are now defined upstream in
`DevelopingPeriodMap.lean`. This file records the compatibility lemmas tying
those axiom-free objects to the canonical arc integral and to the chosen
cycle basis (`loopIntegralToH1`/`periodMapInBasis`), including the agreement
lemma `loopDevValH1Hom_eq_loopIntegralToH1_apply`.
-/

noncomputable section

namespace Jacobians.RiemannSurface

open scoped Manifold Topology
open scoped ContDiff

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

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
