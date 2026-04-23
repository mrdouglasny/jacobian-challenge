/-
# Hyperelliptic curves

A hyperelliptic curve is the compact Riemann surface associated to the
affine equation `y² = f(x)` where `f ∈ ℂ[x]` is a squarefree polynomial
of degree `d ≥ 3`. It is a branched double cover of `ℙ¹` via the `x`
projection, with branch points at the roots of `f` (and sometimes at
infinity, depending on the parity of `d`).

**Genus.** For `f` squarefree of degree `d`:
  - `d = 2g + 1` (odd): genus is `g`, one branch point at `∞`.
  - `d = 2g + 2` (even): genus is `g`, no branch point at `∞`.

So `g = ⌊(d - 1) / 2⌋`.

## Scope of this scaffold

This module defines:
  - `HyperellipticData`: the polynomial `f` together with its
    squarefree/degree hypotheses.
  - `HyperellipticAffine`: the affine part `{(x, y) | y² = f(x)}`.
  - `Hyperelliptic`: the compactified projective model (TODO).

**Full chart construction is not attempted at this pin.** The atlas
requires:
  1. Away-from-branch-points chart: `(x, y) ↦ x`.
  2. At-branch-point chart: a local parameter like `t = √(x - a)` for
     a branch point `a`.
  3. At-infinity chart: `(x, y) ↦ 1/x` (plus a branch resolution if
     `d` is odd).

Each of (2) and (3) requires implicit-function-theorem applications
and careful sign choices. This is a substantial but bounded project;
see `Jacobians/ProjectiveCurve/Charts.lean` for shared machinery.

## Once complete

Hyperelliptic curves provide:
  - Explicit genus via `g = ⌊(d - 1) / 2⌋`; concrete examples for
    every `g ≥ 1`.
  - Explicit holomorphic 1-forms: `x^k dx / y` for `0 ≤ k < g` form a
    basis of `H^0(Ω¹)`. This would let us *prove* `AX_FiniteDimOneForms`
    on hyperelliptic curves concretely (non-axiomatically).
  - Explicit A- and B-cycles: branch-cut contours around pairs of
    branch points, lifted to the two-sheeted cover. Concrete witness
    for `AX_AnalyticCycleBasis` on hyperelliptic curves.
  - Concrete Jacobian: computed via the period matrix with entries
    `∫_{γ_i} x^k dx / y` (hyperelliptic integrals), well-studied
    classical objects.

## References

* Mumford, *Tata Lectures on Theta II*, Ch. IIIa (hyperelliptic
  curves and theta characteristics).
* Farkas & Kra, *Riemann Surfaces*, Ch. III §7 (hyperelliptic
  integrals).
* Miranda, *Algebraic Curves and Riemann Surfaces*, Ch. III §1
  (smooth projective models).
-/
import Jacobians.AbelianVariety.ComplexTorus
import Jacobians.RiemannSurface.Genus

namespace Jacobians.ProjectiveCurve

open scoped Manifold Topology
open scoped ContDiff

/-- Data specifying a hyperelliptic curve: a squarefree polynomial
`f ∈ ℂ[x]` of degree at least 3. -/
structure HyperellipticData where
  /-- The defining polynomial `f` of the hyperelliptic curve `y² = f(x)`. -/
  f : Polynomial ℂ
  /-- Squarefree: the curve has no singularities over the roots of `f`. -/
  h_squarefree : Squarefree f
  /-- Degree `≥ 3` so the genus `g = ⌊(d-1)/2⌋` is positive. -/
  h_degree : 3 ≤ f.natDegree

namespace HyperellipticData

/-- The genus of a hyperelliptic curve: `g = ⌊(d - 1) / 2⌋` where
`d = deg f`. -/
def genus (H : HyperellipticData) : ℕ := (H.f.natDegree - 1) / 2

/-- The curve has a branch point at infinity iff `deg f` is odd. -/
def hasBranchAtInfinity (H : HyperellipticData) : Bool :=
  Odd H.f.natDegree

end HyperellipticData

/-- **Affine hyperelliptic curve**: the subtype `{(x, y) | y² = f(x)}`
of `ℂ²`. Missing the points at infinity (1 or 2 depending on `deg f`
parity).

This is the easy part — a straightforward subtype. The compact
projective model requires adding points at infinity and building charts
there; see TODO below. -/
def HyperellipticAffine (H : HyperellipticData) : Type :=
  { p : ℂ × ℂ // p.2 ^ 2 = H.f.eval p.1 }

/-- **Axiom-stub.** The compactified hyperelliptic curve `y² = f(x)` as
a type. For `deg f = 2g + 1` odd: one branch point at infinity;
for `deg f = 2g + 2` even: two points at infinity. Either way, a
smooth compact Riemann surface.

Classically constructed as a two-sheeted branched cover of `ℙ¹` by
the `x`-projection, with branch points at the roots of `f`. Full atlas
requires:
  (a) affine chart: `(x, y) ↦ x` on the non-branch-point locus.
  (b) branch-point chart: local parameter `t = √(x - a)` at each
      branch point `a` (root of `f`).
  (c) infinity chart: coordinate change `x ↦ 1/x` at ∞.

Axiomatized as a `Type` until the atlas lands (workstream E2). -/
axiom Hyperelliptic (H : HyperellipticData) : Type

/-- Buzzard typeclass instances on `Hyperelliptic H`, axiom-stubbed.
Matches the `PlaneCurve` pattern (E1). Retires when the full atlas
construction is available. -/
axiom Hyperelliptic.instTopologicalSpace (H : HyperellipticData) :
    TopologicalSpace (Hyperelliptic H)
attribute [instance] Hyperelliptic.instTopologicalSpace
axiom Hyperelliptic.instT2Space (H : HyperellipticData) : T2Space (Hyperelliptic H)
attribute [instance] Hyperelliptic.instT2Space
axiom Hyperelliptic.instCompactSpace (H : HyperellipticData) : CompactSpace (Hyperelliptic H)
attribute [instance] Hyperelliptic.instCompactSpace
axiom Hyperelliptic.instConnectedSpace (H : HyperellipticData) : ConnectedSpace (Hyperelliptic H)
attribute [instance] Hyperelliptic.instConnectedSpace
axiom Hyperelliptic.instChartedSpace (H : HyperellipticData) : ChartedSpace ℂ (Hyperelliptic H)
attribute [instance] Hyperelliptic.instChartedSpace
axiom Hyperelliptic.instIsManifold (H : HyperellipticData) :
    IsManifold 𝓘(ℂ, ℂ) ω (Hyperelliptic H)
attribute [instance] Hyperelliptic.instIsManifold

/-- **Axiom.** The genus of `y² = f(x)` matches the combinatorial
formula `⌊(deg f - 1) / 2⌋`. Classical: `H⁰(Ω¹)` is spanned by the
explicit holomorphic differentials `x^k dx/y` for `0 ≤ k < g`.
Mirrors `AX_PluckerFormula` for smooth plane curves. Retires when the
explicit basis is constructed against the Hyperelliptic atlas. -/
axiom AX_Hyperelliptic_genus (H : HyperellipticData) :
    Jacobians.RiemannSurface.genus (Hyperelliptic H) = H.genus

-- TODO (holomorphic differentials): explicit basis of
-- `HolomorphicOneForm (Hyperelliptic H)` given by
-- `ω_k := x^k dx / y` for `0 ≤ k < H.genus`. Gives a concrete proof of
-- `AX_FiniteDimOneForms` for hyperelliptic curves.

-- TODO (A/B cycles): concrete `AnalyticCycleBasis` on hyperelliptic
-- curves via branch-cut contours. Witness that `AX_AnalyticCycleBasis`
-- is non-vacuous for this family.

end Jacobians.ProjectiveCurve
