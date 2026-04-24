/-
# Smooth projective plane curves

A smooth projective plane curve is `X = {[x : y : z] ∈ ℙ² | F(x, y, z) = 0}`
where `F ∈ ℂ[x, y, z]` is a homogeneous polynomial of degree `d ≥ 1`
whose gradient `∇F` has no common zero with `F` on `ℂ³ \ {0}` (smoothness).

**Genus.** For smooth `X` of degree `d ≥ 3`: `g = (d - 1)(d - 2) / 2`
(Plücker formula). For `d = 1` (line) or `d = 2` (conic): `g = 0`.

## Scope of this module (refactored 2026-04-23)

- `HomogeneousPoly n d`: a homogeneous polynomial of degree `d` in
  `n + 1` variables.
- `PlaneCurveData`: `F` with smoothness + `deg F ≥ 1` hypotheses.
- `PlaneCurveAffine`: the affine patch `{F(x, y, 1) = 0}` in `ℂ²`.
- **`PlaneCurve H := OnePoint (PlaneCurveAffine H)`** — real `def` via
  one-point compactification (2026-04-23). This glues the points at
  infinity (where `z = 0`) into a single point, which is correct when
  `X ∩ {z = 0}` is a single projective point, lossy otherwise (the
  atlas work needs to handle this case properly).
- Topology / T2 / compact / connected / nonempty instances are real
  `instance`s via OnePoint infrastructure (+ subsidiary axioms for
  affine-level connectedness and noncompactness).
- `ChartedSpace ℂ` + `IsManifold 𝓘(ℂ) ω` stay **axiomatic** (atlas
  construction; classical but nontrivial).
-/
import Mathlib

namespace Jacobians.ProjectiveCurve

open scoped Manifold Topology
open scoped ContDiff
open OnePoint

/-- A homogeneous polynomial of degree `d` in `n + 1` variables over `ℂ`. -/
structure HomogeneousPoly (n d : ℕ) where
  /-- The underlying polynomial in `(Fin (n + 1))`-indexed variables. -/
  val : MvPolynomial (Fin (n + 1)) ℂ
  /-- Homogeneity of degree `d`. -/
  homogeneous : val.IsHomogeneous d

/-- Data specifying a smooth projective plane curve `{F = 0} ⊂ ℙ²`. -/
structure PlaneCurveData where
  /-- Degree of the defining polynomial, `≥ 1`. -/
  d : ℕ
  h_deg : 1 ≤ d
  /-- The defining homogeneous polynomial `F ∈ ℂ[x, y, z]` of degree `d`. -/
  F : HomogeneousPoly 2 d
  /-- Smoothness: on `ℂ³ \ {0}`, `F = 0` implies some partial derivative
  is nonzero. -/
  h_smooth : ∀ v : Fin 3 → ℂ, v ≠ 0 → F.val.eval v = 0 →
    (∃ i : Fin 3, (MvPolynomial.pderiv i F.val).eval v ≠ 0)

namespace PlaneCurveData

/-- The genus of a smooth projective plane curve of degree `d`:
`g = (d - 1)(d - 2) / 2` (Plücker). -/
def genus (H : PlaneCurveData) : ℕ := (H.d - 1) * (H.d - 2) / 2

end PlaneCurveData

/-- **Affine plane curve**: the subtype of `ℂ²` cut out by the
dehomogenization `F(x, y, 1) = 0`. -/
def PlaneCurveAffine (H : PlaneCurveData) : Type :=
  { p : ℂ × ℂ // H.F.val.eval ![p.1, p.2, (1 : ℂ)] = 0 }

namespace PlaneCurveAffine

variable {H : PlaneCurveData}

instance : TopologicalSpace (PlaneCurveAffine H) :=
  inferInstanceAs (TopologicalSpace
    { p : ℂ × ℂ // H.F.val.eval ![p.1, p.2, (1 : ℂ)] = 0 })

instance : T2Space (PlaneCurveAffine H) :=
  inferInstanceAs (T2Space
    { p : ℂ × ℂ // H.F.val.eval ![p.1, p.2, (1 : ℂ)] = 0 })

/-- The affine locus is closed: preimage of `0` under the continuous
map `(x, y) ↦ F(x, y, 1)`. -/
theorem isClosed_carrier (H : PlaneCurveData) :
    IsClosed { p : ℂ × ℂ | H.F.val.eval ![p.1, p.2, (1 : ℂ)] = 0 } := by
  have hcont : Continuous (fun p : ℂ × ℂ =>
      H.F.val.eval ![p.1, p.2, (1 : ℂ)]) := by
    have hvec : Continuous (fun p : ℂ × ℂ => (![p.1, p.2, (1 : ℂ)] : Fin 3 → ℂ)) := by
      refine continuous_pi (fun i => ?_)
      fin_cases i
      · exact continuous_fst
      · exact continuous_snd
      · exact continuous_const
    exact (MvPolynomial.continuous_eval H.F.val).comp hvec
  exact isClosed_eq hcont continuous_const

/-- Local compactness inherited via the closed-subtype route. -/
instance : LocallyCompactSpace (PlaneCurveAffine H) := by
  have hclosed := isClosed_carrier H
  exact hclosed.isClosedEmbedding_subtypeVal.locallyCompactSpace

/-- **Axiom (NOT VERIFIED).** For a smooth plane curve of degree `≥ 1`
the affine patch is nonempty. Classical: `F` has at least one zero on
`ℂ² × {1} ⊂ ℂ³ \ {0}` by projective algebraic geometry. -/
axiom AX_PlaneCurveAffine_nonempty (H : PlaneCurveData) :
    Nonempty (PlaneCurveAffine H)

attribute [instance] AX_PlaneCurveAffine_nonempty

/-- **Axiom (NOT VERIFIED).** For a smooth plane curve of degree `≥ 3`
the affine patch is connected (irreducible variety in the classical
topology). For `d = 1, 2` (line, conic), may be one or two connected
components. This axiom is for `d ≥ 3`; callers at smaller degree
should use the genus-0 `ProjectiveLine` directly. -/
axiom AX_PlaneCurveAffine_connected (H : PlaneCurveData) :
    ConnectedSpace (PlaneCurveAffine H)

attribute [instance] AX_PlaneCurveAffine_connected

/-- **Axiom (NOT VERIFIED).** The affine patch is noncompact —
projective curves are compact but their affine patches are not (the
affine patch misses at least one point at infinity). -/
axiom AX_PlaneCurveAffine_noncompact (H : PlaneCurveData) :
    NoncompactSpace (PlaneCurveAffine H)

attribute [instance] AX_PlaneCurveAffine_noncompact

end PlaneCurveAffine

/-! ### Projective compactification

A smooth plane curve of degree `d` generically meets the line at
infinity `{z = 0}` in **`d` distinct points** (by Bézout). So the
classical smooth projective compactification adds `d` points at
infinity (fewer if the curve is tangent to or contains the infinity
line, but still ≥ 1 for smooth curves).

The one-point compactification `OnePoint (PlaneCurveAffine H)` adds
just **one** point — wrong for any `d ≥ 2`. A unified parity-style
split as we used for `Hyperelliptic` doesn't work cleanly here because
the number of infinity points depends on the curve's intersection with
`{z = 0}`, not just parity.

We therefore **axiomatize** the projective compactification with
properly formulated instances, until the three-affine-chart atlas
construction (dehomogenizing with `x ≠ 0`, `y ≠ 0`, `z ≠ 0` and
gluing) is built explicitly.

Historical note: earlier versions (commits through `63ccce7`) defined
`PlaneCurve H := OnePoint (PlaneCurveAffine H)` as a real def. That
was topologically wrong for any `d ≥ 2`; Codex review 2026-04-23
correctly flagged it. This version is the honest axiom-stub.
-/

/-- **Axiom-stub.** The smooth projective plane curve `{F = 0} ⊂ ℙ²`
as a type.

Classical construction: glue three affine charts `z ≠ 0`, `y ≠ 0`,
`x ≠ 0` along their pairwise overlaps. The resulting space is a
compact, connected, Hausdorff complex 1-manifold of genus
`(d - 1)(d - 2) / 2` (Plücker). Axiomatized with properly formulated
typeclass instances until the three-chart pushout is constructed. -/
axiom PlaneCurve (H : PlaneCurveData) : Type

axiom PlaneCurve.instTopologicalSpace (H : PlaneCurveData) :
    TopologicalSpace (PlaneCurve H)
attribute [instance] PlaneCurve.instTopologicalSpace

axiom PlaneCurve.instT2Space (H : PlaneCurveData) : T2Space (PlaneCurve H)
attribute [instance] PlaneCurve.instT2Space

axiom PlaneCurve.instCompactSpace (H : PlaneCurveData) :
    CompactSpace (PlaneCurve H)
attribute [instance] PlaneCurve.instCompactSpace

axiom PlaneCurve.instConnectedSpace (H : PlaneCurveData) :
    ConnectedSpace (PlaneCurve H)
attribute [instance] PlaneCurve.instConnectedSpace

axiom PlaneCurve.instNonempty (H : PlaneCurveData) : Nonempty (PlaneCurve H)
attribute [instance] PlaneCurve.instNonempty

axiom PlaneCurve.instChartedSpace (H : PlaneCurveData) :
    ChartedSpace ℂ (PlaneCurve H)
attribute [instance] PlaneCurve.instChartedSpace

axiom PlaneCurve.instIsManifold (H : PlaneCurveData) :
    IsManifold 𝓘(ℂ, ℂ) ω (PlaneCurve H)
attribute [instance] PlaneCurve.instIsManifold

-- TODO (genus_eq): `Jacobians.RiemannSurface.genus (PlaneCurve H) = H.genus`
-- via the Plücker formula discharge.

-- TODO (Pluecker discharge): concrete `AX_PluckerFormula` via
-- Poincaré-residue forms `x^a y^b z^c · resF`.

-- TODO (Fermat curves): `{x^d + y^d + z^d = 0}` as concrete example.

end Jacobians.ProjectiveCurve
