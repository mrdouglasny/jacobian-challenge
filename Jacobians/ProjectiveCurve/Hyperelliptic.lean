/- 
# Hyperelliptic curves

Public wrapper for the hyperelliptic curve models.

- Shared data, affine chart, and odd compactification live in
  `Hyperelliptic/Basic.lean`.
- The even two-chart pushout lives in `Hyperelliptic/Even.lean`.
- The unified `Hyperelliptic H` type and atlas-level axioms remain in
  this file.
-/
import Jacobians.ProjectiveCurve.Hyperelliptic.Basic
import Jacobians.ProjectiveCurve.Hyperelliptic.Even
import Jacobians.ProjectiveCurve.Hyperelliptic.OddAtlas

namespace Jacobians.ProjectiveCurve

open scoped Manifold Topology
open scoped ContDiff
open OnePoint

/-- Hyperelliptic curve with **even** `deg f = 2g + 2`: the real
two-chart pushout construction from `HyperellipticEvenProj`. -/
def HyperellipticEven (H : HyperellipticData) (_h : ¬ Odd H.f.natDegree) : Type :=
  HyperellipticEvenProj H

instance (H : HyperellipticData) (h : ¬ Odd H.f.natDegree) :
    TopologicalSpace (HyperellipticEven H h) :=
  Jacobians.ProjectiveCurve.instTopologicalSpaceHyperellipticEvenProj H

instance (H : HyperellipticData) (h : ¬ Odd H.f.natDegree) :
    T2Space (HyperellipticEven H h) :=
  Jacobians.ProjectiveCurve.instT2SpaceHyperellipticEvenProjOfNotOddNatNatDegreeComplexF H h

instance (H : HyperellipticData) (h : ¬ Odd H.f.natDegree) :
    CompactSpace (HyperellipticEven H h) :=
  Jacobians.ProjectiveCurve.instCompactSpaceHyperellipticEvenProjOfNotOddNatNatDegreeComplexF H h

instance (H : HyperellipticData) (h : ¬ Odd H.f.natDegree) :
    ConnectedSpace (HyperellipticEven H h) :=
  Jacobians.ProjectiveCurve.instConnectedSpaceHyperellipticEvenProjOfNotOddNatNatDegreeComplexF H h

instance (H : HyperellipticData) (h : ¬ Odd H.f.natDegree) :
    Nonempty (HyperellipticEven H h) :=
  Jacobians.ProjectiveCurve.instNonemptyHyperellipticEvenProj H

/-- **Axiom-stub.** The compactified hyperelliptic curve `y² = f(x)`,
as a unified type. Routes conceptually to `HyperellipticOdd H h` in the
odd case and to the now-real `HyperellipticEven H h` construction in
the even case.

Because a unified real `def` via parity dispatch trips Lean's
typeclass resolution on `dite` at the type level, we keep the unified
type itself as an axiom whose intended content is pinned by the
homeomorphism axioms below. -/
axiom Hyperelliptic (H : HyperellipticData) : Type

axiom Hyperelliptic.instTopologicalSpace (H : HyperellipticData) :
    TopologicalSpace (Hyperelliptic H)
attribute [instance] Hyperelliptic.instTopologicalSpace

axiom Hyperelliptic.instT2Space (H : HyperellipticData) : T2Space (Hyperelliptic H)
attribute [instance] Hyperelliptic.instT2Space

axiom Hyperelliptic.instCompactSpace (H : HyperellipticData) :
    CompactSpace (Hyperelliptic H)
attribute [instance] Hyperelliptic.instCompactSpace

axiom Hyperelliptic.instConnectedSpace (H : HyperellipticData) :
    ConnectedSpace (Hyperelliptic H)
attribute [instance] Hyperelliptic.instConnectedSpace

axiom Hyperelliptic.instNonempty (H : HyperellipticData) : Nonempty (Hyperelliptic H)
attribute [instance] Hyperelliptic.instNonempty

/-- **Axiom.** `ChartedSpace ℂ (Hyperelliptic H)` — the atlas
construction. Atlas plan in `docs/hyperelliptic-atlas-plan.md`. -/
axiom Hyperelliptic.instChartedSpace (H : HyperellipticData) :
    ChartedSpace ℂ (Hyperelliptic H)
attribute [instance] Hyperelliptic.instChartedSpace

/-- **Axiom.** `IsManifold 𝓘(ℂ) ω (Hyperelliptic H)` — analyticity of
chart transitions. Part of the atlas construction plan. -/
axiom Hyperelliptic.instIsManifold (H : HyperellipticData) :
    IsManifold 𝓘(ℂ, ℂ) ω (Hyperelliptic H)
attribute [instance] Hyperelliptic.instIsManifold

/-- **Axiom.** For odd `deg f`, the unified `Hyperelliptic H` is
homeomorphic to `HyperellipticOdd H h`. -/
axiom AX_Hyperelliptic_oddEquiv (H : HyperellipticData) (h : Odd H.f.natDegree) :
    Hyperelliptic H ≃ₜ HyperellipticOdd H h

/-- **Axiom.** For even `deg f`, the unified `Hyperelliptic H` is
homeomorphic to `HyperellipticEven H h`. The even target is now a real
construction. -/
axiom AX_Hyperelliptic_evenEquiv (H : HyperellipticData) (h : ¬ Odd H.f.natDegree) :
    Hyperelliptic H ≃ₜ HyperellipticEven H h

/-- **Axiom.** The genus of `y² = f(x)` matches the combinatorial
formula `⌊(deg f - 1) / 2⌋`. -/
axiom AX_Hyperelliptic_genus (H : HyperellipticData) :
    Jacobians.RiemannSurface.genus (Hyperelliptic H) = H.genus

end Jacobians.ProjectiveCurve
