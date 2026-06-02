/-
# σ-anti-invariance of holomorphic 1-forms (route D, P0)

For an arbitrary holomorphic 1-form `ω` on the even hyperelliptic curve, the
goal is `ω.coeff(σq, ·) = −ω.coeff(q, ·)` on smooth-Y projX charts (anti-
invariance, **AI**), the bridge to Liouville L2. See
`docs/route-d-implementation-plan.md` and
`docs/anti-invariance-route-decision.md`.

**P0 (this file, in progress):** the *local* `dx`-coefficient `omegaDx form a` —
ω's coefficient in the affine projection-to-`x` chart at `⟦inl a⟧`, obtained by
transporting `ω.coeff` from the preferred chart. Only **local** analyticity (at
the base x-coordinate) is needed — never analyticity on a full chart target
(that was the σ*-pullback crux; route D's Liouville step needs only pointwise
`AnalyticAt`).
-/
import Jacobians.ProjectiveCurve.Hyperelliptic.Involution
import Jacobians.ProjectiveCurve.Hyperelliptic.AffineForm
import Jacobians.RiemannSurface.OneForm
import Jacobians.GeneralResults.OddPartDslope
import Mathlib.Analysis.Calculus.FDeriv.Analytic

namespace Jacobians.ProjectiveCurve

open scoped Manifold ContDiff Topology
open Jacobians.RiemannSurface

variable {H : HyperellipticData} [Fact (¬ Odd H.f.natDegree)]

/-- The quotient point `⟦inl a⟧` of an affine point `a`. -/
abbrev evenMk (a : HyperellipticAffine H) : HyperellipticEvenProj H :=
  Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a)

/-- The **`dx`-coefficient** of `ω` at an affine point `a`: ω's coefficient in
the lifted affine chart at `⟦inl a⟧`, obtained by transporting `ω.coeff` (given
in the preferred chart `extChartAt ⟦inl a⟧`) through the change-of-chart formula.
For `a ∈ smoothLocusY` the lifted affine chart is the projection-to-`x` chart, so
this is the coefficient of `ω` with respect to `dx`. -/
noncomputable def omegaDx (form : HolomorphicOneForm (HyperellipticEvenProj H))
    (a : HyperellipticAffine H) : ℂ → ℂ :=
  fun x =>
    form.coeff (evenMk a)
        (extChartAt 𝓘(ℂ, ℂ) (evenMk a)
          ((HyperellipticEvenProj.affineLiftChart H Fact.out a).symm x))
      * fderiv ℂ (fun y => extChartAt 𝓘(ℂ, ℂ) (evenMk a)
          ((HyperellipticEvenProj.affineLiftChart H Fact.out a).symm y)) x 1

/-- **P0 deliverable (local analyticity).** `omegaDx form a` is analytic at the
base x-coordinate `a.val.1`. Proof (TODO): `form.coeff (evenMk a)` is analytic on
the preferred chart target (ω's `IsHolomorphicOneFormCoeff`); the *local*
transition `extChartAt ⟦inl a⟧ ∘ (affineLiftChart a).symm` is analytic on the
overlap neighborhood of `a` (both charts in the maximal atlas, via
`affineLiftChart_mem_maximalAtlas` + `StructureGroupoid.compatible_of_mem_maximalAtlas`);
compose, and multiply by the analytic `fderiv` factor. All on a neighborhood of
`a` — never the full target. -/
theorem omegaDx_analyticAt (form : HolomorphicOneForm (HyperellipticEvenProj H))
    {a : HyperellipticAffine H} (hpY : a ∈ HyperellipticAffine.smoothLocusY H) :
    AnalyticAt ℂ (omegaDx form a) a.val.1 := by
  sorry

-- Chart independence across overlapping same-sheet affine charts (the
-- same-sheet projX transition has derivative `1`) belongs to the P3 assembly of
-- the global `s`; its precise statement needs the overlap hypotheses, deferred.

end Jacobians.ProjectiveCurve
