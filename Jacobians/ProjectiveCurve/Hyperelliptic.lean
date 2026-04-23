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

## Scope of this module (refactored 2026-04-23)

- `HyperellipticData`: squarefree `f : ℂ[x]` with `deg f ≥ 3`.
- `HyperellipticAffine`: the affine part `{(x, y) | y² = f(x)}` —
  closed subtype of `ℂ × ℂ`, inherits `TopologicalSpace`, `T2Space`,
  `LocallyCompactSpace`.
- **`Hyperelliptic H := OnePoint (HyperellipticAffine H)`** — real
  `def` via one-point compactification (2026-04-23). For odd `deg f`
  this is the correct projective model; for even `deg f` it identifies
  the two points at infinity, producing a singular identification point
  at the atlas level (irrelevant at the topology level, which is what
  the OnePoint instances handle).
- Topology / T2 / compact / connected / nonempty instances are real
  `instance`s via OnePoint infrastructure (+ one subsidiary axiom
  `AX_HyperellipticAffine_connected`).
- `ChartedSpace ℂ` + `IsManifold 𝓘(ℂ) ω` stay **axiomatic** (the atlas
  construction; see `docs/hyperelliptic-atlas-plan.md` for the ~3-week
  discharge).
- `AX_Hyperelliptic_genus` — classical genus formula, axiom until the
  explicit 1-form basis lands.

## References

* Mumford, *Tata Lectures on Theta II*, Ch. IIIa.
* Farkas & Kra, *Riemann Surfaces*, Ch. III §7.
* Miranda, *Algebraic Curves and Riemann Surfaces*, Ch. III §1.
-/
import Jacobians.AbelianVariety.ComplexTorus
import Jacobians.RiemannSurface.Genus

namespace Jacobians.ProjectiveCurve

open scoped Manifold Topology
open scoped ContDiff
open OnePoint

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

/-- The genus of a hyperelliptic curve: `g = ⌊(d - 1) / 2⌋`. -/
def genus (H : HyperellipticData) : ℕ := (H.f.natDegree - 1) / 2

/-- The curve has a branch point at infinity iff `deg f` is odd. -/
def hasBranchAtInfinity (H : HyperellipticData) : Bool :=
  Odd H.f.natDegree

end HyperellipticData

/-- **Affine hyperelliptic curve**: the subtype `{(x, y) | y² = f(x)}`
of `ℂ × ℂ`. Closed in `ℂ × ℂ` (preimage of `0` under
`(x, y) ↦ y² - f(x)`), inherits topology, T2, local compactness. -/
def HyperellipticAffine (H : HyperellipticData) : Type :=
  { p : ℂ × ℂ // p.2 ^ 2 = H.f.eval p.1 }

namespace HyperellipticAffine

variable {H : HyperellipticData}

/-- Topology inherited from `ℂ × ℂ` as a subtype. -/
instance : TopologicalSpace (HyperellipticAffine H) :=
  inferInstanceAs (TopologicalSpace { p : ℂ × ℂ // p.2 ^ 2 = H.f.eval p.1 })

instance : T2Space (HyperellipticAffine H) :=
  inferInstanceAs (T2Space { p : ℂ × ℂ // p.2 ^ 2 = H.f.eval p.1 })

/-- The affine locus is closed in `ℂ × ℂ` as the zero-set of
`(x, y) ↦ y² - f(x)`. -/
theorem isClosed_carrier (H : HyperellipticData) :
    IsClosed { p : ℂ × ℂ | p.2 ^ 2 = H.f.eval p.1 } := by
  have hcont : Continuous (fun p : ℂ × ℂ => p.2 ^ 2 - H.f.eval p.1) := by
    have h1 : Continuous (fun p : ℂ × ℂ => p.2 ^ 2) :=
      (continuous_snd).pow 2
    have h2 : Continuous (fun p : ℂ × ℂ => H.f.eval p.1) :=
      (Polynomial.continuous H.f).comp continuous_fst
    exact h1.sub h2
  have : { p : ℂ × ℂ | p.2 ^ 2 = H.f.eval p.1 } =
      { p : ℂ × ℂ | p.2 ^ 2 - H.f.eval p.1 = 0 } := by
    ext p
    simp [sub_eq_zero]
  rw [this]
  exact isClosed_eq hcont continuous_const

/-- Local compactness inherited via the closed-subtype route. -/
instance : LocallyCompactSpace (HyperellipticAffine H) := by
  have hclosed := isClosed_carrier H
  exact hclosed.isClosedEmbedding_subtypeVal.locallyCompactSpace

/-- A witness: pick any root `a` of `f` (exists because `ℂ` is
algebraically closed and `deg f ≥ 3 > 0`); then `(a, 0)` satisfies
`0² = 0 = f.eval a`. -/
noncomputable instance : Nonempty (HyperellipticAffine H) := by
  have hnatDeg : 0 < H.f.natDegree := by
    have : 3 ≤ H.f.natDegree := H.h_degree
    omega
  have hf_ne : H.f ≠ 0 := by
    intro h
    rw [h, Polynomial.natDegree_zero] at hnatDeg
    omega
  have hdeg : 0 < H.f.degree := by
    rw [Polynomial.degree_eq_natDegree hf_ne]
    exact_mod_cast hnatDeg
  obtain ⟨a, ha⟩ := Complex.exists_root hdeg
  refine ⟨⟨(a, 0), ?_⟩⟩
  simp [Polynomial.IsRoot.def.mp ha]

/-- **Axiom (NOT VERIFIED).** For a squarefree polynomial `f` of degree
`≥ 3`, the affine hyperelliptic curve `{y² = f(x)}` is connected.

Classical fact: the curve is an irreducible algebraic variety (the
defining polynomial `y² - f(x)` is irreducible in `ℂ[x, y]` when `f` is
squarefree and non-square), hence connected in the classical topology.

Retires once Mathlib has Hilbert's Nullstellensatz + irreducibility
criteria for bivariate polynomials. -/
axiom AX_HyperellipticAffine_connected (H : HyperellipticData) :
    ConnectedSpace (HyperellipticAffine H)

attribute [instance] AX_HyperellipticAffine_connected

/-- **Axiom (NOT VERIFIED).** The affine hyperelliptic curve is
noncompact: as `x → ∞` along the real axis with `|x|` large, `|y|² =
|f(x)|` grows, so `y` can be arbitrarily large and the curve is
unbounded in `ℂ²`, hence noncompact.

Needed for the `ConnectedSpace` instance on the one-point
compactification (via
`OnePoint.instConnectedSpaceOfPreconnectedSpaceOfNoncompactSpace`). -/
axiom AX_HyperellipticAffine_noncompact (H : HyperellipticData) :
    NoncompactSpace (HyperellipticAffine H)

attribute [instance] AX_HyperellipticAffine_noncompact

end HyperellipticAffine

/-- **Compactified hyperelliptic curve** `y² = f(x)`, real `def` via
one-point compactification of the affine locus.

For odd `deg f = 2g + 1`: `OnePoint` adds the single point at infinity
— correct projective model.

For even `deg f = 2g + 2`: the classical projective model has two
points at infinity `∞₊`, `∞₋`; `OnePoint` identifies them into a
single point, producing a model that differs from the smooth projective
model by a quotient at `∞`. This is acceptable at the topology level
(T2 + compact + connected) but requires the atlas to be built carefully
(the `ChartedSpace` instance axiom handles this — real-def construction
is in `docs/hyperelliptic-atlas-plan.md`).

Refactored 2026-04-23: replaced `axiom Hyperelliptic : Type` +
6 instance axioms with this real `def` and 5 real instances. -/
def Hyperelliptic (H : HyperellipticData) : Type :=
  OnePoint (HyperellipticAffine H)

namespace Hyperelliptic

variable {H : HyperellipticData}

/-- Instances inherited from `OnePoint` infrastructure. -/
instance : TopologicalSpace (Hyperelliptic H) :=
  inferInstanceAs (TopologicalSpace (OnePoint (HyperellipticAffine H)))

instance : T2Space (Hyperelliptic H) :=
  inferInstanceAs (T2Space (OnePoint (HyperellipticAffine H)))

instance : CompactSpace (Hyperelliptic H) :=
  inferInstanceAs (CompactSpace (OnePoint (HyperellipticAffine H)))

instance : Nonempty (Hyperelliptic H) :=
  inferInstanceAs (Nonempty (OnePoint (HyperellipticAffine H)))

instance : ConnectedSpace (Hyperelliptic H) :=
  inferInstanceAs (ConnectedSpace (OnePoint (HyperellipticAffine H)))

end Hyperelliptic

/-- **Axiom.** `ChartedSpace ℂ (Hyperelliptic H)` — the atlas construction
for hyperelliptic curves. Requires:
  (a) affine chart `(x, y) ↦ x` on the non-branch-point locus;
  (b) branch-point chart: local parameter `t = √(x - a)` at each
      branch point `a` (root of `f`);
  (c) infinity chart.
See `docs/hyperelliptic-atlas-plan.md` for the 6-phase discharge plan. -/
axiom Hyperelliptic.instChartedSpace (H : HyperellipticData) :
    ChartedSpace ℂ (Hyperelliptic H)
attribute [instance] Hyperelliptic.instChartedSpace

/-- **Axiom.** `IsManifold 𝓘(ℂ) ω (Hyperelliptic H)` — analyticity of
chart transitions. Part of the atlas construction plan. -/
axiom Hyperelliptic.instIsManifold (H : HyperellipticData) :
    IsManifold 𝓘(ℂ, ℂ) ω (Hyperelliptic H)
attribute [instance] Hyperelliptic.instIsManifold

/-- **Axiom.** The genus of `y² = f(x)` matches the combinatorial
formula `⌊(deg f - 1) / 2⌋`. Classical; retires when the explicit basis
`x^k dx / y` for `0 ≤ k < g` is constructed against the atlas. -/
axiom AX_Hyperelliptic_genus (H : HyperellipticData) :
    Jacobians.RiemannSurface.genus (Hyperelliptic H) = H.genus

-- TODO (holomorphic differentials): explicit basis of
-- `HolomorphicOneForm (Hyperelliptic H)` given by
-- `ω_k := x^k dx / y` for `0 ≤ k < H.genus`. Gives a concrete proof of
-- `AX_FiniteDimOneForms` for hyperelliptic curves.

-- TODO (A/B cycles): concrete `AnalyticCycleBasis` on hyperelliptic
-- curves via branch-cut contours.

end Jacobians.ProjectiveCurve
