/-
Period-lattice membership for developing values of arbitrary continuous loops.

The developing-value period vector of ANY continuous loop (at any basepoint)
lies in the period lattice `periodLatticeInBasis` — at the loop's own
basepoint via the `H1` functional `loopDevValH1Hom`, and at every other
basepoint via path conjugation and the developing-value path algebra
(`devVal_trans` / `devVal_symm`).

Consumed by the discharge of `AX_pushforwardAmbient_preserves_lattice`
(issue #30): the image of a lattice vector under the pushforward ambient map
is the period vector of the image loop `f ∘ γ`, which this file places in the
target lattice.
-/
import Jacobians.RiemannSurface.LoopIntegralHom

namespace Jacobians.RiemannSurface

open scoped Manifold Topology
open scoped ContDiff

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  [ConnectedSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

omit [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] in
/-- The `H1` developing-value functional evaluated on the homology class of a
continuous loop `δ` is the developing value of `δ`. -/
theorem loopDevValH1Hom_fromPath (y : Y) (form : HolomorphicOneForm Y)
    (δ : Path y y) :
    loopDevValH1Hom y form
        (Additive.ofMul (Abelianization.of
          (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk δ)))) =
      developingValue y form ((δ : Path y y) : C(unitInterval, Y)) := by
  rw [loopDevValH1Hom_of]
  rfl

/-- The developing-value period vector of a continuous loop lies in the
period lattice based at the loop's basepoint. -/
theorem devVal_loop_mem_periodLatticeInBasis (y : Y)
    (b : Module.Basis (Fin (genus Y)) ℂ (HolomorphicOneForm Y))
    (δ : Path y y) :
    (fun i => developingValue y (b i) ((δ : Path y y) : C(unitInterval, Y))) ∈
      Jacobians.Axioms.periodLatticeInBasis Y y b := by
  have h := loopDevValH1Hom_mem_periodLatticeInBasis y b
    (Additive.ofMul (Abelianization.of
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk δ))))
  have heq : (fun i => developingValue y (b i)
        ((δ : Path y y) : C(unitInterval, Y))) =
      fun i => loopDevValH1Hom y (b i)
        (Additive.ofMul (Abelianization.of
          (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk δ)))) := by
    funext i
    exact (loopDevValH1Hom_fromPath y (b i) δ).symm
  rw [heq]
  exact h

/-- Conjugation transport: the developing-value period vector of a loop at
`y₁` lies in the period lattice based at `y₂`, given a connecting path
`p : Path y₁ y₂`. The conjugated loop `p⁻¹ ⬝ δ ⬝ p` has the same developing
values (`devVal_trans` + `devVal_symm`), and is based at `y₂`. -/
theorem devVal_loop_mem_periodLatticeInBasis_of_path {y₁ y₂ : Y}
    (p : Path y₁ y₂)
    (b : Module.Basis (Fin (genus Y)) ℂ (HolomorphicOneForm Y))
    (δ : Path y₁ y₁) :
    (fun i => developingValue y₁ (b i) ((δ : Path y₁ y₁) : C(unitInterval, Y))) ∈
      Jacobians.Axioms.periodLatticeInBasis Y y₂ b := by
  have hmem := devVal_loop_mem_periodLatticeInBasis y₂ b ((p.symm.trans δ).trans p)
  have heq : (fun i => developingValue y₂ (b i)
        (((p.symm.trans δ).trans p : Path y₂ y₂) : C(unitInterval, Y))) =
      fun i => developingValue y₁ (b i)
        ((δ : Path y₁ y₁) : C(unitInterval, Y)) := by
    funext i
    rw [devVal_trans y₂ (b i) (p.symm.trans δ) p,
      devVal_trans y₂ (b i) p.symm δ,
      devVal_symm y₂ (b i) p]
    have hbase : developingValue y₂ (b i)
          ((δ : Path y₁ y₁) : C(unitInterval, Y)) =
        developingValue y₁ (b i) ((δ : Path y₁ y₁) : C(unitInterval, Y)) :=
      developingValue_basepoint_indep y₂ y₁ (b i) _
    rw [hbase]
    ring
  rw [heq] at hmem
  exact hmem

/-- The developing-value period vector of any continuous loop lies in the
period lattice at ANY basepoint — the connected charted space `Y` is
path-connected (charts are locally path-connected), so a connecting path
always exists. -/
theorem devVal_loop_mem_periodLatticeInBasis_any (y₀ : Y) {y₁ : Y}
    (b : Module.Basis (Fin (genus Y)) ℂ (HolomorphicOneForm Y))
    (δ : Path y₁ y₁) :
    (fun i => developingValue y₁ (b i) ((δ : Path y₁ y₁) : C(unitInterval, Y))) ∈
      Jacobians.Axioms.periodLatticeInBasis Y y₀ b := by
  haveI : LocPathConnectedSpace Y :=
    ChartedSpace.locPathConnectedSpace (H := ℂ) (M := Y)
  haveI : PathConnectedSpace Y := PathConnectedSpace.of_locPathConnectedSpace
  exact devVal_loop_mem_periodLatticeInBasis_of_path
    (PathConnectedSpace.somePath y₁ y₀) b δ

end Jacobians.RiemannSurface
