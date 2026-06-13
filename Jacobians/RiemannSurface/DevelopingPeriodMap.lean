/-
# The axiom-free developing-value period map

This file builds the homology-level period pairing
`H1 X x₀ →+ (HolomorphicOneForm X →ₗ[ℂ] ℂ)` directly from the developing
value, with **no chosen cycle basis** — the `ℤ`-linear extension over `H1`
comes from `Abelianization.lift` (universal property of abelianization), and
the `ℂ`-linearity in the form comes from `developingValue`'s linearity in the
form (`DevelopingValueForm.lean`).

The construction here is moved upstream of `LoopIntegral.lean` so that the
official `loopIntegralToH1` / `periodMap` can be re-founded on it, removing
`AX_PeriodCycleBasis` from their kernel closure.

## Main definitions

* `loopDevValQuotient`, `loopDevValHom`, `loopDevValH1Hom` — the developing
  value descended to homotopy classes, the fundamental group, and `H1`.
* `developingPeriodMap` — the period pairing as
  `H1 X x₀ →+ (HolomorphicOneForm X →ₗ[ℂ] ℂ)`.
-/
import Jacobians.RiemannSurface.HomotopyInvarianceDevelop
import Jacobians.RiemannSurface.Homology
import Jacobians.RiemannSurface.DevelopingBridge
import Jacobians.RiemannSurface.DevelopingValueForm

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

/-- On a generator, the developing-value functional is the developing value of
the representing path. -/
theorem loopDevValH1Hom_of_apply (x₀ : X) (form : HolomorphicOneForm X)
    (γ : FundamentalGroup X x₀) :
    loopDevValH1Hom x₀ form (Additive.ofMul (Abelianization.of γ)) =
      loopDevValQuotient x₀ form (FundamentalGroup.toPath γ) :=
  rfl

/-! ## Linearity in the form -/

/-- The developing-value functional is additive in the form: the two additive
homomorphisms `H1 →+ ℂ` agree on the generators (where the statement is
`developingValue_add`), hence everywhere. -/
theorem loopDevValH1Hom_add_form (x₀ : X) (form₁ form₂ : HolomorphicOneForm X) :
    loopDevValH1Hom x₀ (form₁ + form₂) =
      loopDevValH1Hom x₀ form₁ + loopDevValH1Hom x₀ form₂ := by
  ext γ
  change loopDevValH1Hom x₀ (form₁ + form₂) (Additive.ofMul (Abelianization.of γ)) =
    loopDevValH1Hom x₀ form₁ (Additive.ofMul (Abelianization.of γ)) +
      loopDevValH1Hom x₀ form₂ (Additive.ofMul (Abelianization.of γ))
  simp only [loopDevValH1Hom_of_apply]
  induction γ using Path.Homotopic.Quotient.ind with
  | mk γp =>
    simp only [FundamentalGroup.toPath, loopDevValQuotient_mk]
    exact developingValue_add x₀ form₁ form₂ _

/-- The developing-value functional is homogeneous in the form. -/
theorem loopDevValH1Hom_smul_form (x₀ : X) (a : ℂ) (form : HolomorphicOneForm X) :
    loopDevValH1Hom x₀ (a • form) = a • loopDevValH1Hom x₀ form := by
  ext γ
  change loopDevValH1Hom x₀ (a • form) (Additive.ofMul (Abelianization.of γ)) =
    (a • loopDevValH1Hom x₀ form) (Additive.ofMul (Abelianization.of γ))
  simp only [AddMonoidHom.smul_apply, smul_eq_mul, loopDevValH1Hom_of_apply]
  induction γ using Path.Homotopic.Quotient.ind with
  | mk γp =>
    simp only [FundamentalGroup.toPath, loopDevValQuotient_mk]
    simpa [smul_eq_mul] using developingValue_smul x₀ a form _

/-! ## The form-linear period map -/

/-- The homology-level period pairing built from the developing value:
`H1 X x₀ →+ (HolomorphicOneForm X →ₗ[ℂ] ℂ)`. For a fixed homology class `h`,
the value is the `ℂ`-linear functional `form ↦ loopDevValH1Hom x₀ form h`;
`ℤ`-additivity in `h` is `loopDevValH1Hom`'s additivity. **Axiom-free.** -/
noncomputable def developingPeriodMap (x₀ : X) :
    H1 X x₀ →+ (HolomorphicOneForm X →ₗ[ℂ] ℂ) where
  toFun h :=
    { toFun := fun form => loopDevValH1Hom x₀ form h
      map_add' := fun f g => by
        rw [loopDevValH1Hom_add_form]; rfl
      map_smul' := fun a f => by
        rw [loopDevValH1Hom_smul_form]; rfl }
  map_zero' := by ext form; simp
  map_add' h₁ h₂ := by ext form; simp

@[simp] theorem developingPeriodMap_apply (x₀ : X) (h : H1 X x₀)
    (form : HolomorphicOneForm X) :
    developingPeriodMap x₀ h form = loopDevValH1Hom x₀ form h :=
  rfl

end Jacobians.RiemannSurface
