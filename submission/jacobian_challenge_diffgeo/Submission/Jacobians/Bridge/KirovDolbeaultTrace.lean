/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Submission.Jacobians.Bridge.KirovHolomorphicEquiv
import Submission.KirovDolbeault.TraceForm

/-!
# Bridge: the Kirov-Dolbeault trace (`traceFormTotal`) on our 1-forms

Phase-D bridge file (Dolbeault-port program cluster C; issues #26/#27/#28).
The port's `Jacobians.traceFormTotal` — the genuine fibre-sum trace
`f₊ : Ω¹(X) →ₗ[ℂ] Ω¹(Y)` of a holomorphic map of compact Riemann surfaces,
zero on constant maps — is transported to our cocycle representation
`HolomorphicOneForm` by composing two linear equivalences:

* `bridgeFormEquiv : HolomorphicOneForm X ≃ₗ[ℂ]
  Vendor.Kirov.HolomorphicOneForms X` (cocycle ↔ bundle-section,
  `Bridge/KirovHolomorphicEquiv.lean`);
* `kdFormAlign : Vendor.Kirov.HolomorphicOneForms X ≃ₗ[ℂ]
  Jacobians.HolomorphicOneForms X` (vendored copy ↔ port original) — the
  two types unfold to the *identical* `ContMDiffSection` type with the
  identical instances (the vendored signature merely carries an extra
  `[Nonempty X]`, here derivable from `[ConnectedSpace X]`), so the
  alignment is the identity linear equivalence.

This file consumes only sorry-free port results: `traceFormTotal`,
`traceFormTotal_id`, `traceFormTotal_comp`, `traceFormTotal_eq_zero_of_const`
are kernel-verified to `[propext, Classical.choice, Quot.sound]`. It backs
the in-place conversion of `Axioms.pushforwardOneForm` (+ `_id`, `_comp`)
from axioms to a def/theorems in `Jacobians/Axioms/AbelJacobiMap.lean`.
-/

noncomputable section

open scoped Manifold ContDiff Bundle

namespace Jacobians.Bridge

open Jacobians.RiemannSurface

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- Identity-shaped alignment between the vendored Kirov form space
`Jacobians.Vendor.Kirov.HolomorphicOneForms` and the Dolbeault port's
`Jacobians.HolomorphicOneForms`: both are by definition the same
`ContMDiffSection` type of the holomorphic cotangent bundle. -/
def kdFormAlign :
    Jacobians.Vendor.Kirov.HolomorphicOneForms X ≃ₗ[ℂ]
      _root_.Jacobians.HolomorphicOneForms X :=
  LinearEquiv.refl ℂ (ContMDiffSection 𝓘(ℂ) (ℂ →L[ℂ] ℂ) ω
    (fun x : X => TangentSpace 𝓘(ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))

/-- Composite bridge: our cocycle holomorphic 1-forms are linearly
equivalent to the Dolbeault port's bundle-section holomorphic 1-forms. -/
def bridgeKDFormEquiv :
    HolomorphicOneForm X ≃ₗ[ℂ] _root_.Jacobians.HolomorphicOneForms X :=
  (bridgeFormEquiv (X := X)).trans kdFormAlign

end Jacobians.Bridge
