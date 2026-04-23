/-
`HolomorphicOneForm ProjectiveLine` is a subsingleton.

**Claim.** On the Riemann sphere there are no nonzero holomorphic
1-forms: `Subsingleton (HolomorphicOneForm ProjectiveLine)`.

**Classical proof.** Any holomorphic 1-form `ω` on `ℙ¹(ℂ)` has a
representative `a(z) dz` in the standard affine chart, holomorphic on
`ℂ`. The chart transition to the infinity chart is `w = 1/z`, so in
the infinity chart the coefficient becomes `-a(1/w) / w²`, which must
also be holomorphic at `w = 0`. The only `a` making `a(1/w)/w²`
bounded at `w = 0` is `a ≡ 0`.

**Our proof routes through genus.** We have
`genus_projectiveLine_eq_zero : genus ProjectiveLine = 0` (from
`Line/Genus.lean`), and by definition `genus X = finrank ℂ
(HolomorphicOneForm X)`. Combined with the finite-dimensional instance
`instFiniteDimOneForms`, `finrank = 0` forces the module to be a
subsingleton.
-/
import Jacobians.ProjectiveCurve.Line.Genus
import Jacobians.Axioms.FiniteDimOneForms

namespace Jacobians.ProjectiveCurve

open scoped Manifold Topology
open scoped ContDiff
open Jacobians Jacobians.RiemannSurface

/-- On `ProjectiveLine`, every holomorphic 1-form is zero. Derived from
`genus_projectiveLine_eq_zero` + finite-dimensionality of the
holomorphic 1-forms. -/
instance instSubsingletonHolomorphicOneFormProjectiveLine :
    Subsingleton (HolomorphicOneForm ProjectiveLine) := by
  have h : Module.finrank ℂ (HolomorphicOneForm ProjectiveLine) = 0 :=
    genus_projectiveLine_eq_zero
  exact Module.finrank_zero_iff.mp h

/-- On `ProjectiveLine`, every holomorphic 1-form equals zero. -/
theorem HolomorphicOneForm_projectiveLine_eq_zero
    (form : HolomorphicOneForm ProjectiveLine) : form = 0 :=
  Subsingleton.elim _ _

end Jacobians.ProjectiveCurve
