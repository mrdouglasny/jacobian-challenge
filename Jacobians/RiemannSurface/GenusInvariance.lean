import Jacobians.RiemannSurface.Genus
import Jacobians.Axioms.AbelJacobiMap

namespace Jacobians.RiemannSurface

open scoped Manifold Topology
open scoped ContDiff
open Jacobians.Axioms

/-- Pullback along a biholomorphism and its inverse compose to the identity on
holomorphic one-forms on the source. -/
theorem pullbackOneForm_comp_symm
    {X Y : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
      [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
      [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (e : X ≃ Y) (he : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω e)
    (he' : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω e.symm) :
    (pullbackOneForm (e : X → Y) he).comp
      (pullbackOneForm (e.symm : Y → X) he') = LinearMap.id := by
  rw [← AX_pullbackOneForm_comp (f := (e : X → Y)) (hf := he)
    (g := (e.symm : Y → X)) (hg := he')]
  simpa [Function.comp_def] using (AX_pullbackOneForm_id (X := X))

/-- Pullback along the inverse biholomorphism and then the biholomorphism
compose to the identity on holomorphic one-forms on the target. -/
theorem pullbackOneForm_symm_comp
    {X Y : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
      [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
      [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (e : X ≃ Y) (he : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω e)
    (he' : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω e.symm) :
    (pullbackOneForm (e.symm : Y → X) he').comp
      (pullbackOneForm (e : X → Y) he) = LinearMap.id := by
  rw [← AX_pullbackOneForm_comp (f := (e.symm : Y → X)) (hf := he')
    (g := (e : X → Y)) (hg := he)]
  simpa [Function.comp_def] using (AX_pullbackOneForm_id (X := Y))

/-- A biholomorphism induces a linear equivalence on holomorphic one-forms by
contravariant pullback. -/
noncomputable def holomorphicOneFormLinearEquivOfBiholo
    {X Y : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
      [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
      [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (e : X ≃ Y) (he : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω e)
    (he' : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω e.symm) :
    HolomorphicOneForm Y ≃ₗ[ℂ] HolomorphicOneForm X :=
  LinearEquiv.ofLinear (pullbackOneForm (e : X → Y) he)
    (pullbackOneForm (e.symm : Y → X) he')
    (pullbackOneForm_comp_symm e he he')
    (pullbackOneForm_symm_comp e he he')

/-- The genus of a compact Riemann surface is invariant under biholomorphism. -/
theorem genus_eq_of_biholo
    {X Y : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
      [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
      [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (e : X ≃ Y) (he : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω e) (he' : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω e.symm) :
    genus X = genus Y := by
  exact (LinearEquiv.finrank_eq (holomorphicOneFormLinearEquivOfBiholo e he he')).symm

end Jacobians.RiemannSurface
