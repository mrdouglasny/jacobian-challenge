/-
  Čech finiteness — definition of the sup-norm cochain geometry `DiskOverlapData`.

  This file isolates `DiskOverlapData` and its componentwise Banach/Montel properties
  to prevent circular dependencies between `CechFinitenessWiring` and `CechModelGeometry`.
-/
import Jacobians.Dolbeault.CechFinitenessAbstract
import Jacobians.Dolbeault.BddHol
import Jacobians.Dolbeault.CechModelBridge

open Jacobians.Dolbeault.CechFiniteness ContinuousLinearMap
open BoundedContinuousFunction
open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Sup-norm cochain geometry.** The finite pair-index `J` of a Leray chart-disk cover, with, for
each overlap `p`, the chart-image cover-open `Uov p ⊆ ℂ` and a relatively-compact convex shrinking
`Kov p ⋐ Uov p`. This is exactly the geometric input the disk-Montel atom needs (open `U`, compact
convex `K ⊆ U`). The cover 1-cochains live in `Π_p BddHol (Uov p)`, the shrinking 1-cochains in
`Π_p (Kov p →ᵇ ℂ)`. -/
structure DiskOverlapData where
  /-- The finite pair-index of the cover (overlaps). -/
  J : Type
  [fintypeJ : Fintype J]
  [decEqJ : DecidableEq J]
  /-- Chart-image of each overlap on the COVER (an open set in `ℂ`). -/
  Uov : J → Set ℂ
  hUov : ∀ p, IsOpen (Uov p)
  /-- The relatively-compact SHRINKING of each overlap (a compact set in `ℂ`).  No convexity is
  required: the restriction operator is compact for any compact `K ⊆ U`
  (`BddHol.isCompactOperator_restrictCLM_of_compact`), so `Kov` can be a chart-image of an overlap
  (which is NOT convex across charts). -/
  Kov : J → Set ℂ
  hKcpt : ∀ p, IsCompact (Kov p)
  hKU : ∀ p, Kov p ⊆ Uov p

attribute [instance] DiskOverlapData.fintypeJ DiskOverlapData.decEqJ

namespace DiskOverlapData

variable (d : DiskOverlapData)

/-- Each shrinking compact carries a `CompactSpace` (so `Kov p →ᵇ ℂ` is a Banach space). -/
noncomputable instance compactSpace (p : d.J) : CompactSpace (d.Kov p) :=
  isCompact_iff_compactSpace.mp (d.hKcpt p)

/-- COVER 1-cochains: bounded-holomorphic on each overlap chart-image. -/
abbrev Ccov : Type := ∀ p : d.J, BddHol (d.Uov p)

/-- SHRINKING 1-cochains: bounded-continuous on each compact shrunk overlap (where the Montel atom
lands). -/
abbrev Cshr : Type := ∀ p : d.J, (d.Kov p →ᵇ ℂ)

noncomputable instance : NormedAddCommGroup d.Ccov := inferInstance
noncomputable instance : NormedSpace ℂ d.Ccov := inferInstance
noncomputable instance : NormedAddCommGroup d.Cshr := inferInstance
noncomputable instance : NormedSpace ℂ d.Cshr := inferInstance

/-- `Π_p BddHol (Uov p)` is a Banach space (finite product of the Banach `BddHol`). -/
noncomputable instance : CompleteSpace d.Ccov := by
  haveI : ∀ p, CompleteSpace (BddHol (d.Uov p)) := fun p => BddHol.completeSpace (d.hUov p)
  infer_instance

/-- `Π_p (Kov p →ᵇ ℂ)` is a Banach space. -/
noncomputable instance : CompleteSpace d.Cshr := inferInstance

/-! ### STEP 2/3 — the restriction operator `ρ` cover → shrinking, and its compactness -/

/-- The raw cochain restriction `Π_p BddHol (Uov p) →L[ℂ] Π_p (Kov p →ᵇ ℂ)`, componentwise
`BddHol.restrictCLM`. -/
noncomputable def rhoRaw : d.Ccov →L[ℂ] d.Cshr :=
  ContinuousLinearMap.pi (fun p => (BddHol.restrictCLM (d.hKU p)).comp (proj p))

@[simp] theorem rhoRaw_apply (f : d.Ccov) (p : d.J) :
    d.rhoRaw f p = BddHol.restrictCLM (d.hKU p) (f p) := by
  simp only [rhoRaw, ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply]

/-- **STEP 3 (the Montel payoff).** The cochain restriction `ρ` (cover → shrinking) is a COMPACT
operator: componentwise it is `BddHol.restrictCLM`, compact by the disk-Montel atom
(`BddHol.isCompactOperator_restrictCLM_of_compact`, valid for any compact shrunk overlap — no
convexity), and a finite product of compacts is compact (`isCompactOperator_pi`). -/
theorem rhoRaw_compact : IsCompactOperator d.rhoRaw := by
  apply isCompactOperator_pi (fun p => BddHol.restrictCLM (d.hKU p))
  intro p
  exact BddHol.isCompactOperator_restrictCLM_of_compact (d.hUov p) (d.hKcpt p) (d.hKU p)

end DiskOverlapData

end Jacobians.Dolbeault
