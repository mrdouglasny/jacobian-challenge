/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Jacobians.RiemannSurface.MeromorphicFunctionField

/-!
# The Riemann-Roch space `L(D)`

This file anchors the textbook Riemann-Roch space attached to a divisor.  For
Forster, *Lectures on Riemann Surfaces*, §16, this is
`L(D) = H^0(X, O(D))`: meromorphic functions `f` satisfying `div(f) + D ≥ 0`.

The bridge to the existing opaque `H0` API is deferred to a single theorem at
the end of the file.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

open scoped Manifold Topology ContDiff

namespace Jacobians.RiemannSurface

open Jacobians.Axioms
open Jacobians.Vendor.Wallace.HolomorphicForms.VanishingOrder

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ⊤ X]

/-- An effective divisor is a formal integer combination of points whose
coefficients are all nonnegative.  This is the coefficientwise positivity
predicate on `Divisor X = FreeAbelianGroup X`, the positivity condition used in
Forster, *Lectures on Riemann Surfaces*, §16 for `L(D) = H^0(X, O(D))`. -/
def Effective (D : Divisor X) : Prop :=
  ∀ p : X, 0 ≤ FreeAbelianGroup.coeff p (D : FreeAbelianGroup X)

@[simp]
theorem effective_zero : Effective (0 : Divisor X) := by
  intro p
  simp

@[simp]
theorem effective_of (p : X) : Effective (FreeAbelianGroup.of p : Divisor X) := by
  classical
  intro q
  change 0 ≤ FreeAbelianGroup.toFinsupp (FreeAbelianGroup.of p) q
  by_cases h : q = p
  · subst q
    simp
  · simp [h]

theorem Effective.add {D E : Divisor X} (hD : Effective D) (hE : Effective E) :
    Effective (D + E) := by
  intro p
  simpa using add_nonneg (hD p) (hE p)

@[simp]
theorem meromorphicAtX_zero (p : X) :
    MeromorphicAtX (0 : X → ℂ) p := by
  simpa [MeromorphicAtX, Function.comp_def] using
    (MeromorphicAt.const (0 : ℂ) ((extChartAt 𝓘(ℂ) p) p))

@[simp]
theorem orderAt_zero (p : X) :
    orderAt p (0 : X → ℂ) = ⊤ := by
  rw [orderAt]
  simpa [Function.comp_def] using
    (meromorphicOrderAt_const ((extChartAt 𝓘(ℂ) p) p) (0 : ℂ))

theorem MeromorphicAtX.add {f g : X → ℂ} {p : X}
    (hf : MeromorphicAtX f p) (hg : MeromorphicAtX g p) :
    MeromorphicAtX (f + g) p := by
  simpa [MeromorphicAtX, Function.comp_def, Pi.add_apply] using hf.add hg

theorem min_le_orderAt_add {f g : X → ℂ} {p : X}
    (hf : MeromorphicAtX f p) (hg : MeromorphicAtX g p) :
    min (orderAt p f) (orderAt p g) ≤ orderAt p (f + g) := by
  simpa [orderAt, Function.comp_def, Pi.add_apply] using
    (meromorphicOrderAt_add hf hg)

theorem MeromorphicAtX.const_smul (c : ℂ) {f : X → ℂ} {p : X}
    (hf : MeromorphicAtX f p) :
    MeromorphicAtX (c • f) p := by
  have hc : MeromorphicAt (fun _ : ℂ => c) ((extChartAt 𝓘(ℂ) p) p) :=
    MeromorphicAt.const c ((extChartAt 𝓘(ℂ) p) p)
  simpa [MeromorphicAtX, Function.comp_def, Pi.smul_apply, smul_eq_mul] using
    hc.smul hf

theorem orderAt_const_smul_of_ne_zero {c : ℂ} (hc : c ≠ 0) (p : X) (f : X → ℂ) :
    orderAt p (c • f) = orderAt p f := by
  have hconst : AnalyticAt ℂ (fun _ : ℂ => c) ((extChartAt 𝓘(ℂ) p) p) :=
    analyticAt_const
  simpa [orderAt, Function.comp_def, Pi.smul_apply, smul_eq_mul] using
    (meromorphicOrderAt_smul_of_ne_zero
      (x := (extChartAt 𝓘(ℂ) p) p)
      (g := fun _ : ℂ => c)
      (f := f ∘ (extChartAt 𝓘(ℂ) p).symm) hconst hc)

/-- The Riemann-Roch space `L(D)` as a genuine complex subspace of functions:
`L(D) = { f meromorphic on X | div(f) + D ≥ 0 } = H^0(X, O(D))` in the
textbook notation of Forster, *Lectures on Riemann Surfaces*, §16.  With the
Wallace convention, the condition is `ord_p(f) ≥ -coeff_p(D)` for every point,
and the identically zero function is included because its order is `⊤`. -/
def riemannRochSpace (D : Divisor X) : Submodule ℂ (X → ℂ) where
  carrier :=
    { f : X → ℂ |
      (∀ p : X, MeromorphicAtX f p) ∧
        ∀ p : X,
          ((-(FreeAbelianGroup.coeff p (D : FreeAbelianGroup X)) : ℤ) : WithTop ℤ) ≤
            orderAt p f }
  zero_mem' := by
    constructor
    · exact meromorphicAtX_zero
    · intro p
      rw [orderAt_zero]
      exact le_top
  add_mem' := by
    rintro f g ⟨hf_mer, hf_ord⟩ ⟨hg_mer, hg_ord⟩
    constructor
    · intro p
      exact (hf_mer p).add (hg_mer p)
    · intro p
      exact (le_min (hf_ord p) (hg_ord p)).trans
        (min_le_orderAt_add (hf_mer p) (hg_mer p))
  smul_mem' := by
    rintro c f ⟨hf_mer, hf_ord⟩
    by_cases hc : c = 0
    · subst c
      constructor
      · intro p
        simpa using (meromorphicAtX_zero (X := X) p)
      · intro p
        simpa [Pi.smul_apply, orderAt_zero] using
          (le_top :
            ((-(FreeAbelianGroup.coeff p (D : FreeAbelianGroup X)) : ℤ) : WithTop ℤ) ≤
              (⊤ : WithTop ℤ))
    · constructor
      · intro p
        exact MeromorphicAtX.const_smul c (hf_mer p)
      · intro p
        rw [orderAt_const_smul_of_ne_zero hc p f]
        exact hf_ord p

/-- Deferred comparison between the existing opaque `H0` formulation and the
real Riemann-Roch space `L(D) = H^0(X, O(D))` of Forster, *Lectures on Riemann
Surfaces*, §16.  This is intentionally the only theorem in this file whose
proof is still opaque. -/
theorem H0_equiv_riemannRochSpace (D : Divisor X) :
    Nonempty (H0 (LineBundle.ofDivisor D) ≃ₗ[ℂ] riemannRochSpace D) := by
  sorry

end Jacobians.RiemannSurface
