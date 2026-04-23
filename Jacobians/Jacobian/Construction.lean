/-
Bridge from the Riemann-surface scaffolding to `AbelianVariety.ComplexTorus`.

## Design

Buzzard's challenge wants `Jacobian (X : Type u) : Type u` charted over
`Fin (genus X) → ℂ`, not over the dual space
`(HolomorphicOneForm X →ₗ[ℂ] ℂ)`. Two obstacles:

1. **Dual ChartedSpace.** To avoid having two competing `ChartedSpace`
   instances on the quotient, this module bakes a chosen basis of
   `HolomorphicOneForm X` into the construction. `jacobianBasis X :=
   Module.finBasis ℂ (HolomorphicOneForm X)`, baseline:
   `periodLatticeInBasis X x₀ b` lives in `Fin (genus X) → ℂ`.

2. **Universe lift.** `ComplexTorus (Fin (genus X) → ℂ) _` lives in
   `Type`, but Buzzard's signature says `Jacobian : Type u`. We
   therefore wrap the concrete torus in `ULift.{u, 0}` and transport
   the manifold structure through `Homeomorph.ulift`.

The basepoint is extracted from `[ConnectedSpace X]` (which extends
`Nonempty X`) via `Classical.arbitrary`. Basepoint-independence of
the lattice is not proved here — it needs `AX_RiemannBilinear`.

## Scope

Provides the `Jacobian X` type plus all seven Buzzard typeclass
instances at the `Type u` level, ready to drop into `Challenge.lean`
via `inferInstance`.

The `LieAddGroup` instance requires `IsTopologicalAddGroup (ULift _)`
and `ContMDiff` of add/neg through ULift — a substantial chunk of
additional transfer lemmas. Left unproven here (Challenge.lean's
`instance : LieAddGroup ... := sorry` remains).
-/
import Jacobians.AbelianVariety.ComplexTorus
import Jacobians.Axioms.PeriodLattice

namespace Jacobians

open scoped Manifold Topology
open scoped ContDiff
open Jacobians.RiemannSurface
open Jacobians.Axioms
open Jacobians.AbelianVariety

/-! ### Generic ULift transfer helpers -/

section ULiftTransfer

variable {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

/-- Charts on `ULift M` obtained by composing charts on `M` with the
ULift homeomorphism. -/
@[reducible] noncomputable def chartedSpaceULift : ChartedSpace H (ULift M) where
  atlas := Set.image
    (fun chart => Homeomorph.ulift.toOpenPartialHomeomorph.trans chart)
    (ChartedSpace.atlas (H := H) (M := M))
  chartAt p :=
    Homeomorph.ulift.toOpenPartialHomeomorph.trans (ChartedSpace.chartAt p.down)
  mem_chart_source p := by
    simp only [OpenPartialHomeomorph.trans_toPartialEquiv, PartialEquiv.trans_source,
      Homeomorph.toOpenPartialHomeomorph_source, OpenPartialHomeomorph.toFun_eq_coe,
      Homeomorph.toOpenPartialHomeomorph_apply, Set.univ_inter, Set.mem_preimage]
    exact ChartedSpace.mem_chart_source p.down
  chart_mem_atlas p :=
    ⟨ChartedSpace.chartAt p.down, ChartedSpace.chart_mem_atlas p.down, rfl⟩

/-- The transition map between two ULift-composed charts agrees (on
source) with the corresponding transition map downstairs. -/
lemma ulift_charts_eqOnSource {Y Z : Type*} [TopologicalSpace Y]
    [TopologicalSpace Z] (h : ULift.{u} Y ≃ₜ Y)
    (a b : OpenPartialHomeomorph Y Z) :
    (h.toOpenPartialHomeomorph.trans a).symm.trans
        (h.toOpenPartialHomeomorph.trans b) ≈ a.symm.trans b := by
  calc (h.toOpenPartialHomeomorph.trans a).symm.trans
          (h.toOpenPartialHomeomorph.trans b)
      = (a.symm.trans h.toOpenPartialHomeomorph.symm).trans
          (h.toOpenPartialHomeomorph.trans b) := by
        rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
    _ = a.symm.trans
          ((h.toOpenPartialHomeomorph.symm.trans
            h.toOpenPartialHomeomorph).trans b) := by
        rw [OpenPartialHomeomorph.trans_assoc,
          OpenPartialHomeomorph.trans_assoc]
    _ ≈ a.symm.trans ((OpenPartialHomeomorph.ofSet
            h.toOpenPartialHomeomorph.target (by
              simp [Homeomorph.toOpenPartialHomeomorph])).trans b) := by
        exact OpenPartialHomeomorph.EqOnSource.trans' (Setoid.refl _)
          (OpenPartialHomeomorph.EqOnSource.trans'
            (OpenPartialHomeomorph.symm_trans_self _) (Setoid.refl _))
    _ = a.symm.trans ((OpenPartialHomeomorph.ofSet
            Set.univ isOpen_univ).trans b) := by
        simp [Homeomorph.toOpenPartialHomeomorph]
    _ ≈ a.symm.trans b := by
        refine OpenPartialHomeomorph.EqOnSource.trans' (Setoid.refl _) ?_
        rw [OpenPartialHomeomorph.ofSet_univ_eq_refl,
          OpenPartialHomeomorph.refl_trans]

/-- `HasGroupoid` transfers from `M` to `ULift M` under the charted-space
structure `chartedSpaceULift`. -/
@[reducible] noncomputable def uliftHasGroupoid {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {I : ModelWithCorners ℂ E H} {n : WithTop ℕ∞}
    [HasGroupoid M (contDiffGroupoid n I)] :
    letI : ChartedSpace H (ULift M) := chartedSpaceULift
    HasGroupoid (ULift M) (contDiffGroupoid n I) := by
  letI : ChartedSpace H (ULift M) := chartedSpaceULift
  refine ⟨?_⟩
  rintro e e' ⟨a, haMem, rfl⟩ ⟨b, hbMem, rfl⟩
  exact StructureGroupoid.mem_of_eqOnSource _
    (HasGroupoid.compatible haMem hbMem)
    (ulift_charts_eqOnSource Homeomorph.ulift a b)

end ULiftTransfer

/-! ### Jacobian construction -/

/-- The chosen basis used to write the Jacobian ambient space in the
concrete coordinates `Fin (genus X) → ℂ`. This is `Module.finBasis`, so the
index type is definitionally `Fin (genus X)`. -/
noncomputable def jacobianBasis (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] :
    Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X) :=
  Module.finBasis ℂ (HolomorphicOneForm X)

/-- The concrete (Type 0) Jacobian: complex torus `(Fin (genus X) → ℂ) /
periodLatticeInBasis`. Uses `abbrev` so `ComplexTorus`'s typeclass
instances are available transparently. -/
noncomputable abbrev JacobianAmbient (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] : Type :=
  ComplexTorus (Fin (genus X) → ℂ)
    (periodLatticeInBasis X (Classical.arbitrary X) (jacobianBasis X))

/-- The Jacobian of `X`, universe-lifted to `Type u` to match Buzzard's
signature. Concretely it is `ULift (JacobianAmbient X)`; all seven
Buzzard-required typeclass instances are provided below. -/
noncomputable def Jacobian (X : Type u) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] : Type u :=
  ULift.{u, 0} (JacobianAmbient X)

namespace Jacobian

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- Instances inherited from `JacobianAmbient` via `ULift`. -/
noncomputable instance : AddCommGroup (Jacobian X) :=
  inferInstanceAs (AddCommGroup (ULift (JacobianAmbient X)))

noncomputable instance : TopologicalSpace (Jacobian X) :=
  inferInstanceAs (TopologicalSpace (ULift (JacobianAmbient X)))

noncomputable instance : T2Space (Jacobian X) :=
  inferInstanceAs (T2Space (ULift (JacobianAmbient X)))

noncomputable instance : CompactSpace (Jacobian X) :=
  inferInstanceAs (CompactSpace (ULift (JacobianAmbient X)))

/-- ChartedSpace on `Jacobian X` via the ULift transfer. -/
noncomputable instance : ChartedSpace (Fin (genus X) → ℂ) (Jacobian X) :=
  chartedSpaceULift (H := Fin (genus X) → ℂ) (M := JacobianAmbient X)

/-- HasGroupoid (implicit in IsManifold) transfers through ULift. -/
noncomputable instance :
    HasGroupoid (Jacobian X) (contDiffGroupoid ω 𝓘(ℂ, Fin (genus X) → ℂ)) :=
  uliftHasGroupoid (H := Fin (genus X) → ℂ) (M := JacobianAmbient X)

/-- `IsManifold` on `Jacobian X` via `HasGroupoid` + `IsManifold.mk'`. -/
noncomputable instance :
    IsManifold (𝓘(ℂ, Fin (genus X) → ℂ)) ω (Jacobian X) :=
  IsManifold.mk' _ _ _

-- `LieAddGroup (𝓘(ℂ, Fin (genus X) → ℂ)) ω (Jacobian X)`:
-- transfer through ULift requires `IsTopologicalAddGroup (ULift _)` and
-- `ContMDiff` of add/neg under the ULift chart structure. This is a
-- substantial additional project and is left unfinished. The sorry at
-- `Jacobians/Challenge.lean:86` for this instance remains.

end Jacobian

end Jacobians
