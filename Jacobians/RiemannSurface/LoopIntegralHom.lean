import Jacobians.RiemannSurface.HomotopyInvarianceDevelop
import Jacobians.RiemannSurface.Homology
import Jacobians.RiemannSurface.DevelopingBridge
import Jacobians.Axioms.AnalyticCycleBasis

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

/-- Compatibility on the chosen analytic cycle-basis loops. -/
theorem loopDevValH1Hom_cycleBasis_loop {X : Type*} [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (x₀ : X) (i : Fin (2 * genus X))
    (form : HolomorphicOneForm X) :
    let cb := Classical.choice (Jacobians.Axioms.AX_AnalyticCycleBasis x₀)
    loopDevValH1Hom x₀ form (Jacobians.Axioms.loopToHomology (cb.loops i)) =
      canonicalArcIntegral (cb.loops i).arc form := by
  exact loopDevValH1Hom_loopToHomology x₀ form
    ((Classical.choice (Jacobians.Axioms.AX_AnalyticCycleBasis x₀)).loops i)

end Jacobians.RiemannSurface
