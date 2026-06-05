/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Jacobians.RiemannSurface.MeromorphicFunctionField
import Jacobians.ProjectiveCurve.Line

/-!
# From global meromorphic functions to the Riemann sphere

This file starts the construction of the map from a nonzero global
meromorphic function to `ℙ¹(ℂ)`.

The value at a non-pole is defined by the punctured-neighborhood limit of the
meromorphic germ, not by the representative's raw value.  This is necessary
because `MeromorphicFunctionField X` is a quotient by punctured-germ equality,
and Mathlib's `MeromorphicAt` intentionally ignores the value at the point.
-/

noncomputable section

set_option linter.unusedSectionVars false

open scoped Manifold Topology ContDiff
open Filter OnePoint

open Jacobians.ProjectiveCurve
open Jacobians.Vendor.Wallace.HolomorphicForms.VanishingOrder

namespace Jacobians.RiemannSurface
namespace MeromorphicFunctionField

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ⊤ X]

/-- In a chart, a representative has a finite punctured-neighborhood limit at
every non-pole. -/
private theorem regularValueRep_exists (f : Rep X) (p : X)
    (h_nonpole : 0 ≤ orderAt p (f : X → ℂ)) :
    ∃ c : ℂ,
      Tendsto ((f : X → ℂ) ∘ (chartAt ℂ p).symm)
        (𝓝[≠] (chartAt ℂ p p)) (𝓝 c) := by
  have hf :
      MeromorphicAt ((f : X → ℂ) ∘ (chartAt ℂ p).symm)
        (chartAt ℂ p p) := by
    have h := f.meromorphicAt p
    unfold MeromorphicAtX at h
    rwa [extChartAt_symm_eq_chartAt_symm, extChartAt_eq_chartAt] at h
  have h_nonpole' :
      0 ≤ meromorphicOrderAt ((f : X → ℂ) ∘ (chartAt ℂ p).symm)
        (chartAt ℂ p p) := by
    simpa [orderAt_eq_chartAt] using h_nonpole
  exact tendsto_nhds_of_meromorphicOrderAt_nonneg hf h_nonpole'

/-- The finite value of a representative at a non-pole, defined as the
punctured-neighborhood limit of its chart-local germ.  At poles the value is
irrelevant junk. -/
private noncomputable def regularValueRep (f : Rep X) (p : X) : ℂ :=
  if h : 0 ≤ orderAt p (f : X → ℂ) then
    Classical.choose (regularValueRep_exists f p h)
  else
    0

private theorem regularValueRep_spec (f : Rep X) (p : X)
    (h_nonpole : 0 ≤ orderAt p (f : X → ℂ)) :
    Tendsto ((f : X → ℂ) ∘ (chartAt ℂ p).symm)
      (𝓝[≠] (chartAt ℂ p p)) (𝓝 (regularValueRep f p)) := by
  rw [regularValueRep, dif_pos h_nonpole]
  exact Classical.choose_spec (regularValueRep_exists f p h_nonpole)

private theorem regularValueRep_congr {f g : Rep X} (hfg : Rep.Rel f g) (p : X)
    (h_nonpole : 0 ≤ orderAt p (f : X → ℂ)) :
    regularValueRep f p = regularValueRep g p := by
  have h_order : orderAt p (f : X → ℂ) = orderAt p (g : X → ℂ) :=
    Rep.rel_orderAt hfg p
  have h_nonpole_g : 0 ≤ orderAt p (g : X → ℂ) := by
    rwa [← h_order]
  have hf_lim := regularValueRep_spec f p h_nonpole
  have hg_lim := regularValueRep_spec g p h_nonpole_g
  exact tendsto_nhds_unique (hf_lim.congr' (hfg p)) hg_lim

/-- Representative-level map to `ℙ¹(ℂ)`: poles go to `∞`; non-poles go to
the punctured-germ limit. -/
private noncomputable def toP1Rep (f : Rep X) : X → ProjectiveLine :=
  fun p =>
    if orderAt p (f : X → ℂ) < 0 then
      (∞ : ProjectiveLine)
    else
      ((regularValueRep f p : ℂ) : ProjectiveLine)

private theorem toP1Rep_congr {f g : Rep X} (hfg : Rep.Rel f g) :
    toP1Rep f = toP1Rep g := by
  funext p
  have h_order : orderAt p (f : X → ℂ) = orderAt p (g : X → ℂ) :=
    Rep.rel_orderAt hfg p
  by_cases hpole : orderAt p (f : X → ℂ) < 0
  · have hpole_g : orderAt p (g : X → ℂ) < 0 := by
      rwa [← h_order]
    simp [toP1Rep, hpole, hpole_g]
  · have hpole_g : ¬ orderAt p (g : X → ℂ) < 0 := by
      rwa [← h_order]
    have h_nonpole : 0 ≤ orderAt p (f : X → ℂ) := not_lt.mp hpole
    have h_value : regularValueRep f p = regularValueRep g p :=
      regularValueRep_congr hfg p h_nonpole
    simp [toP1Rep, hpole, hpole_g, h_value]

/-- The meromorphic function's map to the Riemann sphere.  Poles map to `∞`;
non-poles map to the punctured-germ limit in the finite chart. -/
noncomputable def toP1 (f : MeromorphicFunctionField X) : X → ProjectiveLine :=
  Quotient.lift (fun f : Rep X => toP1Rep f)
    (fun _ _ hfg => toP1Rep_congr hfg) f

@[simp]
theorem toP1_mk (f : Rep X) :
    toP1 (Quotient.mk (Rep.setoid (X := X)) f) = toP1Rep f := rfl

theorem toP1_eq_infty_iff (f : MeromorphicFunctionField X) (p : X) :
    toP1 f p = (∞ : ProjectiveLine) ↔ orderAtMF p f < 0 := by
  refine Quotient.inductionOn f ?_
  intro f
  by_cases hpole : orderAt p (f : X → ℂ) < 0
  · simp [toP1, toP1Rep, orderAtMF, hpole]
  · simp [toP1, toP1Rep, orderAtMF, hpole]

theorem toP1_infty_fiber_finite (f : MeromorphicFunctionField X) :
    (toP1 f ⁻¹' ({(∞ : ProjectiveLine)} : Set ProjectiveLine)).Finite := by
  refine (orderSupport_finite f).subset ?_
  intro p hp
  rw [Set.mem_preimage, Set.mem_singleton_iff] at hp
  rw [Set.mem_setOf_eq]
  exact (toP1_eq_infty_iff f p).1 hp |>.ne

/-- Nonconstancy of a meromorphic-function-field element as seen by its
associated map to `ℙ¹(ℂ)`. -/
def Nonconstant (f : MeromorphicFunctionField X) : Prop :=
  ¬ ∃ y₀ : ProjectiveLine, ∀ x : X, toP1 f x = y₀

theorem toP1_nonconst {f : MeromorphicFunctionField X} (hf : Nonconstant f) :
    ¬ ∃ y₀ : ProjectiveLine, ∀ x : X, toP1 f x = y₀ :=
  hf

end MeromorphicFunctionField
end Jacobians.RiemannSurface
