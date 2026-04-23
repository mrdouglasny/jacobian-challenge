/-
`genus (Elliptic ω₁ ω₂ h) = 1`.

## Classical content

An elliptic curve is topologically a 2-torus, and the space of
holomorphic 1-forms on a compact complex torus is 1-dimensional,
spanned by the invariant form `dz` (pulled back from the universal
cover `ℂ`). Hence `genus = 1`.

## Proof route

Route 1 (direct): construct `invariantOneForm : HolomorphicOneForm
(Elliptic ω₁ ω₂ h)` via the constant-1 coefficient family, and show:
  (a) it's a valid element of the submodule (analyticity + cocycle);
  (b) it's non-zero;
  (c) every element of the submodule is a scalar multiple of it
      (via compactness of the torus + Liouville-type argument).

Step (c) is the substantial piece — requires an analysis of the
cotangent cocycle on `ComplexTorus`'s explicit chart atlas (chart
transitions are translations by lattice vectors, so `fderiv = 1`).
With that, a form with coefficient `coeff p` has `coeff p = coeff q`
for all `p, q` (the coefficient is "invariant"), hence is a constant
function of `p`. The ℂ-module structure then gives 1-dim.

Route 2 (via uniformization): no direct uniformization axiom for
genus 1 exists. We'd axiomatize `genus_eq_one_iff_torus` analogous
to the genus-0 case, but this is further from what's needed.

## Current approach (scaffold)

Axiomatize `genus_Elliptic_eq_one` directly as a classical fact.
Route-1 proof will retire the axiom once the analysis is in place.

See `docs/completion-plan.md` workstream B2.
Reference: Mumford, *Tata Lectures on Theta I*, Ch. I §1; Silverman,
*The Arithmetic of Elliptic Curves*, Ch. VI §5 (for the analytic
isomorphism).
-/
import Jacobians.ProjectiveCurve.Elliptic
import Jacobians.RiemannSurface.OneForm
import Jacobians.RiemannSurface.Genus

namespace Jacobians.ProjectiveCurve

open scoped Manifold Topology
open scoped ContDiff
open Jacobians.RiemannSurface

/-- **Axiom.** The genus of any elliptic curve `ℂ / (ℤω₁ + ℤω₂)` is 1.

Classical fact: the space of holomorphic 1-forms on a compact complex
1-torus is 1-dimensional, spanned by the pullback of `dz` from the
universal cover. Retires to a theorem when Route 1 above is
implemented. -/
axiom AX_genus_Elliptic_eq_one (ω₁ ω₂ : ℂ)
    (h : LinearIndependent ℝ ![ω₁, ω₂]) :
    Jacobians.RiemannSurface.genus (Elliptic ω₁ ω₂ h) = 1

-- TODO (invariant form): construct
--
--   noncomputable def invariantOneForm : HolomorphicOneForm (Elliptic ω₁ ω₂ h) :=
--     ⟨fun _ _ => 1, by
--       refine ⟨fun _ => analyticOn_const, ?_⟩
--       intro x y z hz hyzy
--       -- Need: 1 = 1 * fderiv (chart transition) z 1
--       -- For ComplexTorus, chart transitions are translations: fderiv = 1
--       -- so RHS = 1 * 1 = 1.
--       sorry⟩
--
-- Requires detailed access to ComplexTorus's chart atlas — specifically
-- that transition maps are translations with `fderiv = 1`.
-- See `Jacobians/AbelianVariety/ComplexTorus.lean` for the atlas.

-- TODO (spanning): show every holomorphic 1-form on Elliptic is a scalar
-- multiple of the invariant form. Uses compactness + bounded entire =
-- constant (Liouville-style) on the lift to the universal cover.

-- TODO (genus theorem, retires axiom): combining invariant + spanning,
-- `Module.finrank ℂ (HolomorphicOneForm (Elliptic ω₁ ω₂ h)) = 1`.

end Jacobians.ProjectiveCurve
