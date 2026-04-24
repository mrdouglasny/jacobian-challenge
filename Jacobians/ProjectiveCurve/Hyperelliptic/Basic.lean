/- 
# Hyperelliptic curves: basic definitions

Shared definitions for hyperelliptic curves:

- `HyperellipticData`
- `HyperellipticAffine`
- subsidiary affine-chart axioms
- `HyperellipticOdd`

The even pushout construction lives in `Hyperelliptic/Even.lean`, and
the public wrapper file `Hyperelliptic.lean` imports both this file and
the even construction.
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
of `ℂ × ℂ`. Closed in `ℂ × ℂ`, so it inherits topology, T2, and local
compactness. -/
def HyperellipticAffine (H : HyperellipticData) : Type :=
  { p : ℂ × ℂ // p.2 ^ 2 = H.f.eval p.1 }

namespace HyperellipticAffine

variable {H : HyperellipticData}

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

instance : LocallyCompactSpace (HyperellipticAffine H) := by
  have hclosed := isClosed_carrier H
  exact hclosed.isClosedEmbedding_subtypeVal.locallyCompactSpace

/-- A witness: pick a root `a` of `f`, then `(a, 0)` lies on the affine
curve. -/
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

/-- **Axiom (NOT VERIFIED).** The affine hyperelliptic curve is
connected. -/
axiom AX_HyperellipticAffine_connected (H : HyperellipticData) :
    ConnectedSpace (HyperellipticAffine H)

attribute [instance] AX_HyperellipticAffine_connected

/-- **Axiom (NOT VERIFIED).** The affine hyperelliptic curve is
noncompact. -/
axiom AX_HyperellipticAffine_noncompact (H : HyperellipticData) :
    NoncompactSpace (HyperellipticAffine H)

attribute [instance] AX_HyperellipticAffine_noncompact

end HyperellipticAffine

/-- Hyperelliptic curve with **odd** `deg f = 2g + 1`: a single branch
point at infinity, modeled by the one-point compactification of the
affine locus. -/
def HyperellipticOdd (H : HyperellipticData) (_h : Odd H.f.natDegree) : Type :=
  OnePoint (HyperellipticAffine H)

namespace HyperellipticOdd

variable {H : HyperellipticData} {h : Odd H.f.natDegree}

instance : TopologicalSpace (HyperellipticOdd H h) :=
  inferInstanceAs (TopologicalSpace (OnePoint (HyperellipticAffine H)))

instance : T2Space (HyperellipticOdd H h) :=
  inferInstanceAs (T2Space (OnePoint (HyperellipticAffine H)))

instance : CompactSpace (HyperellipticOdd H h) :=
  inferInstanceAs (CompactSpace (OnePoint (HyperellipticAffine H)))

instance : Nonempty (HyperellipticOdd H h) :=
  inferInstanceAs (Nonempty (OnePoint (HyperellipticAffine H)))

instance : ConnectedSpace (HyperellipticOdd H h) :=
  inferInstanceAs (ConnectedSpace (OnePoint (HyperellipticAffine H)))

end HyperellipticOdd

end Jacobians.ProjectiveCurve
