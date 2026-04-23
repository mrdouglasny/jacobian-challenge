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
and `ContMDiff` of add/neg through ULift. A universe-level Set-cast
obstacle was identified (see below) and the instance is currently
**axiomatized** as `AX_jacobian_lieAddGroup` in
`Jacobians/Axioms/AbelJacobiMap.lean` rather than proved here.
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
Buzzard-required typeclass instances are provided below.

`abbrev` (not `def`) so typeclass search sees through to
`ULift (JacobianAmbient X)` — needed by downstream users who write
`Homeomorph.ulift : Jacobian X → JacobianAmbient X` and expect to
find the ChartedSpace instance on the ULift. -/
noncomputable abbrev Jacobian (X : Type u) [TopologicalSpace X] [T2Space X]
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

/-- The target-chart source on `Jacobian X` pulls back through `ULift.up`
to the ambient source. -/
theorem extChartAt_source_up_iff {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (y : Jacobian X) (w : JacobianAmbient X) :
    ULift.up w ∈ (extChartAt (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) y).source ↔
      w ∈ (extChartAt (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) y.down).source := by
  rw [extChartAt_source, extChartAt_source]
  change ULift.up w ∈
      (Homeomorph.ulift.toOpenPartialHomeomorph.trans
        (ChartedSpace.chartAt (H := Fin (genus X) → ℂ) y.down)).source ↔
    w ∈ (ChartedSpace.chartAt (H := Fin (genus X) → ℂ) y.down).source
  constructor <;> intro h <;>
    simpa only [OpenPartialHomeomorph.trans_toPartialEquiv, PartialEquiv.trans_source,
      Homeomorph.toOpenPartialHomeomorph_source, OpenPartialHomeomorph.toFun_eq_coe,
      Homeomorph.toOpenPartialHomeomorph_apply, Set.univ_inter, Set.mem_preimage] using h

/-- Helper: the ULift chart-factoring identity. Saved for future LieAddGroup work. -/
lemma chartAt_jacobian_eq_chartAt_down {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (p : Jacobian X) (z : Jacobian X) :
    (chartAt (Fin (genus X) → ℂ) p) z = (chartAt (Fin (genus X) → ℂ) p.down) z.down :=
  rfl

/-- Helper: the ULift chart-transition identity. Saved for future LieAddGroup work. -/
lemma extChartAt_ulift_comp_down {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (p : Jacobian X) (q : JacobianAmbient X) :
    ((extChartAt (𝓘(ℂ, Fin (genus X) → ℂ)) q) ∘
     (ULift.down : Jacobian X → JacobianAmbient X) ∘
     (extChartAt (𝓘(ℂ, Fin (genus X) → ℂ)) p).symm) =
    ((extChartAt (𝓘(ℂ, Fin (genus X) → ℂ)) q) ∘
     (extChartAt (𝓘(ℂ, Fin (genus X) → ℂ)) p.down).symm) := by
  funext w
  rfl

/-- The chart targets on `Jacobian X` and `JacobianAmbient X` agree propositionally. -/
theorem extChartAt_target_iff {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (p : Jacobian X) (z : Fin (genus X) → ℂ) :
    z ∈ (extChartAt (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) p).target ↔
      z ∈ (extChartAt (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) p.down).target := by
  constructor
  · intro hz
    have hs : (extChartAt (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) p).symm z ∈
        (extChartAt (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) p).source :=
      (extChartAt (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) p).map_target hz
    have hs' :
        ULift.down ((extChartAt (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) p).symm z) ∈
          (extChartAt (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) p.down).source := by
      exact (extChartAt_source_up_iff (X := X) p
        (ULift.down ((extChartAt (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) p).symm z))).1
          (by simpa using hs)
    have hz' :
        extChartAt (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) p.down
          (ULift.down ((extChartAt (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) p).symm z)) = z := by
      simpa [extChartAt, chartedSpaceULift, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm]
        using (extChartAt (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) p).right_inv hz
    exact hz' ▸
      (extChartAt (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) p.down).map_source hs'
  · intro hz
    have hs : (extChartAt (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) p.down).symm z ∈
        (extChartAt (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) p.down).source :=
      (extChartAt (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) p.down).map_target hz
    have hs' :
        ULift.up ((extChartAt (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) p.down).symm z) ∈
          (extChartAt (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) p).source := by
      exact (extChartAt_source_up_iff (X := X) p
        ((extChartAt (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) p.down).symm z)).2 hs
    have hz' :
        extChartAt (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) p
          (ULift.up ((extChartAt (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) p.down).symm z)) = z := by
      simpa [extChartAt, chartedSpaceULift, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm]
        using (extChartAt (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) p.down).right_inv hz
    exact hz' ▸
      (extChartAt (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) p).map_source hs'

/-- `ULift.up` is smooth for the Jacobian charted-space transfer. -/
theorem contMDiff_ulift_up {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] :
    ContMDiff (modelWithCornersSelf ℂ (Fin (genus X) → ℂ))
      (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω
      (ULift.up : JacobianAmbient X → Jacobian X) := by
  have hid :
      ContMDiff (modelWithCornersSelf ℂ (Fin (genus X) → ℂ))
        (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω
        (fun z : JacobianAmbient X => z) := contMDiff_id
  rw [contMDiff_iff] at hid ⊢
  constructor
  · simpa using (Homeomorph.ulift : Jacobian X ≃ₜ JacobianAmbient X).symm.continuous
  · intro x y
    convert hid.2 x y.down using 1
    ext z
    constructor
    · rintro ⟨hz₁, hz₂⟩
      refine ⟨hz₁, ?_⟩
      simpa [Set.mem_preimage] using
        (extChartAt_source_up_iff (X := X) y
          ((extChartAt (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) x).symm z)).1 hz₂
    · rintro ⟨hz₁, hz₂⟩
      refine ⟨hz₁, ?_⟩
      simpa [Set.mem_preimage] using
        (extChartAt_source_up_iff (X := X) y
          ((extChartAt (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) x).symm z)).2 hz₂

/-- `ULift.down` is smooth for the Jacobian charted-space transfer. -/
theorem contMDiff_ulift_down {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] :
    ContMDiff (modelWithCornersSelf ℂ (Fin (genus X) → ℂ))
      (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω
      (ULift.down : Jacobian X → JacobianAmbient X) := by
  have hid :
      ContMDiff (modelWithCornersSelf ℂ (Fin (genus X) → ℂ))
        (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω
        (fun z : JacobianAmbient X => z) := contMDiff_id
  rw [contMDiff_iff] at hid ⊢
  constructor
  · simpa using (Homeomorph.ulift : Jacobian X ≃ₜ JacobianAmbient X).continuous
  · intro p q
    refine (hid.2 p.down q).mono ?_
    intro z hz
    rcases hz with ⟨hz₁, hz₂⟩
    refine ⟨(extChartAt_target_iff (X := X) p z).1 hz₁, ?_⟩
    simpa [Set.mem_preimage, Function.comp, extChartAt_ulift_comp_down (p := p) (q := q)] using hz₂

/-- `LieAddGroup` transfers from the ambient torus to the ULifted Jacobian. -/
noncomputable instance {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] :
    LieAddGroup (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω (Jacobian X) := by
  refine { contMDiff_add := ?_, contMDiff_neg := ?_ }
  · let I := modelWithCornersSelf ℂ (Fin (genus X) → ℂ)
    let hdownProd :
        ContMDiff (I.prod I) (I.prod I) ω
          (fun p : Jacobian X × Jacobian X => (p.1.down, p.2.down)) :=
      (contMDiff_ulift_down (X := X).comp contMDiff_fst).prodMk
        (contMDiff_ulift_down (X := X).comp contMDiff_snd)
    let haddAmbient :
        ContMDiff (I.prod I) I ω
          (fun p : JacobianAmbient X × JacobianAmbient X => p.1 + p.2) :=
      contMDiff_add I ω
    let hup : ContMDiff I I ω (ULift.up : JacobianAmbient X → Jacobian X) :=
      contMDiff_ulift_up (X := X)
    simpa [I] using hup.comp (haddAmbient.comp hdownProd)
  · let I := modelWithCornersSelf ℂ (Fin (genus X) → ℂ)
    let hnegAmbient :
        ContMDiff I I ω (fun p : JacobianAmbient X => -p) :=
      contMDiff_neg I ω
    let hup : ContMDiff I I ω (ULift.up : JacobianAmbient X → Jacobian X) :=
      contMDiff_ulift_up (X := X)
    simpa [I] using hup.comp (hnegAmbient.comp (contMDiff_ulift_down (X := X)))

end Jacobian

end Jacobians
