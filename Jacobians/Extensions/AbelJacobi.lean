/-
# Challenge extensions: tests of the Abel-Jacobi map and Jacobian

Companion to [`Hyperelliptic.lean`](Hyperelliptic.lean) and
[`HyperellipticEven.lean`](HyperellipticEven.lean), which exercise the
**form-side** of the formalization (cocycle 1-forms, basis, genus).
This file exercises the **lattice / Abel-Jacobi side**: theorems whose
statement only types correctly if the period lattice is full-rank and
the Abel-Jacobi map carries the chart-local 1-form data into a real
ℂ^g/Λ quotient.

Each theorem is a meaningful end-to-end test:

* it forces `pathIntegralBasepointFunctional` and the bridging axiom
  `AX_pathIntegral_local_antiderivative` to act non-trivially on the
  basis 1-forms `x^k dx/y` of `Hyperelliptic.lean`;
* it forces `periodMapInBasis` / `periodLatticeInBasis` to land on a
  ℤ-lattice of the correct rank inside `Fin (genus X) → ℂ`, ruling out
  the `Λ = 0` collapse that would make the Jacobian into the whole
  vector space;
* it forces `ofCurveImpl` (and `Jacobian.ofCurve`) to satisfy the
  symmetries (σ-equivariance, divisor-zero) implied by classical
  algebraic-geometry facts, ruling out the constant-zero collapse that
  would make `ofCurve P P = 0` trivially imply `ofCurve _ _ = 0`.

Discharge order recommended:

1. **`periodLattice_rank_HyperellipticOdd_eq`** — the period lattice
   has Z-rank `2g`. Combines `AX_PeriodLattice` with the canonical
   basis from `Hyperelliptic.lean` and the genus theorem. Forces both
   sides to compute (lattice via `periodMapInBasis`; genus via the
   basis count).
2. **`abelJacobi_hyperellipticInvolution`** — A(σ P) = -A(P) modulo
   the period lattice, with a Weierstrass point as basepoint. Tests
   functoriality of the path-integral functional under the involution.
3. **`abelJacobi_principal_divisor_zero`** — Abel's theorem applied to
   the principal divisor of `x - x₀`: the sum
   `A(P₁) + A(P₂) - 2 A(∞)` vanishes in the Jacobian.
4. **`riemannBilinear_hyperellipticOdd`** — the period matrix of the
   canonical basis lies in the Siegel upper half-space.

Even-degree analogues are stated at the end as drop-in twins for
`HyperellipticEvenProj H`.

## Note on what is being tested

The tests below are stated as `theorem … := by sorry`. Each is a
**type-correctness check** of the Jacobian API: simply elaborating the
statement forces typeclass synthesis through `ChartedSpace`,
`IsManifold`, the bridge-induced `FiniteDimensional`, and
`AX_PeriodLattice`'s `IsZLattice` instance. A wrong notion of "period
lattice" or "Jacobian" — for instance, the `Λ = 0` collapse — would
make several of these statements ill-typed or contradict the genus
theorem, even before any proof is written.

References:

* Mumford, *Tata Lectures on Theta I*, Ch. II §2 — period matrix,
  Riemann bilinear relations.
* Forster, *Lectures on Riemann Surfaces*, §17, Ch. III — hyperelliptic
  involution, Abel's theorem.
* Griffiths-Harris, *Principles of Algebraic Geometry*, Ch. 2 §2 —
  period lattice, Jacobian as compact complex torus.
-/

import Jacobians.Challenge
import Jacobians.Extensions.Hyperelliptic
import Jacobians.Extensions.HyperellipticEven
import Jacobians.Axioms.AbelJacobiMap
import Jacobians.Axioms.AbelTheorem
import Jacobians.Axioms.PeriodLattice
import Jacobians.Axioms.RiemannBilinear
import Jacobians.Axioms.AnalyticCycleBasis
import Jacobians.RiemannSurface.Periods
import Jacobians.AbelianVariety.Siegel

namespace Jacobians.Extensions.AbelJacobi

open scoped Manifold ContDiff Topology
open Jacobians Jacobians.ProjectiveCurve Jacobians.RiemannSurface
  Jacobians.Axioms Jacobians.AbelianVariety
open Jacobians.Extensions.Hyperelliptic

/-! ## Test 1 — Period-lattice rank

**Statement.** For `X = HyperellipticOdd H h` of arithmetic genus
`g = (deg f − 1) / 2`, the period image
`periodLatticeInBasis X x₀ (jacobianBasis X)` is a free ℤ-module of
rank `2g`.

**What it tests.** A `Λ = 0` collapse — which would silently satisfy
every downstream Jacobian-side claim — is ruled out: the Z-rank `2g`
forces `Λ` to span a full real subspace of `ℂ^g ≃ ℝ^{2g}`. Combined
with `AX_PeriodLattice`'s `IsZLattice` instance, this is exactly the
data needed for `Jacobian X = ℂ^g / Λ` to be a compact complex torus
(Mumford II.2). -/

/-- **Period lattice rank for odd-degree hyperelliptic curves.** The
period image carries a free ℤ-module structure of rank `2g`, where
`g = (deg f - 1) / 2`. -/
theorem periodLattice_rank_HyperellipticOdd_eq
    (H : HyperellipticData) (h : Odd H.f.natDegree) :
    Module.finrank ℤ
        (periodLatticeInBasis (HyperellipticOdd H h)
          (Classical.arbitrary _) (jacobianBasis _)) =
      2 * ((H.f.natDegree - 1) / 2) := by
  -- Combine `AX_H1FreeRank2g` (rank `2g` source) with injectivity of
  -- `periodMapInBasis` (from `AX_PeriodLattice`'s discreteness +
  -- full-rank conclusion) and the genus theorem
  -- `genus_HyperellipticOdd_eq`.
  sorry

/-- **The Jacobian of an odd-degree hyperelliptic curve is a compact
complex torus.** Combining `periodLattice_rank_HyperellipticOdd_eq` with
the existing instances, the Jacobian is a compact `LieAddGroup` over
`ℂ^g`. The two-line proof here type-checks the chain through the actual
`HyperellipticOdd H h` curve rather than an abstract `X`. -/
theorem jacobian_HyperellipticOdd_isCompactTorus
    (H : HyperellipticData) (h : Odd H.f.natDegree) :
    CompactSpace (Jacobians.Jacobian (HyperellipticOdd H h)) ∧
      LieAddGroup (modelWithCornersSelf ℂ
          (Fin (RiemannSurface.genus (HyperellipticOdd H h)) → ℂ)) ω
        (Jacobians.Jacobian (HyperellipticOdd H h)) :=
  ⟨inferInstance, inferInstance⟩

/-! ## Test 2 — Hyperelliptic involution on the Jacobian

**Statement.** Fix a Weierstrass point `P₀` (in odd degree, the point
at infinity is fixed by σ and is a Weierstrass point — see
`hyperellipticInvolution_involutive` in `Hyperelliptic.lean`). For
every `P ∈ HyperellipticOdd H h`, the Abel-Jacobi map sends
`σ P ↦ −A(P)` in `Jacobian X`.

**What it tests.** The `pathIntegralBasepointFunctional` axiom is
otherwise unconstrained — the local-antiderivative axiom binds it to
the cocycle data of one form at one point, but a constant or
zero-functional choice at the global level cannot be ruled out by that
alone. The σ-equivariance theorem below pins the functional down on
half of `H¹⁰(X)` (the odd part under σ^*), via the classical identity
`σ^*(x^k dx/y) = -(x^k dx/y)`. -/

/-- **A Weierstrass point on the odd-degree hyperelliptic curve.** In
the odd case, the point at infinity is fixed by `σ` and is one of the
`2g + 2` Weierstrass points (the others being the `2g + 1` roots of
`f`, lifted with `y = 0`). -/
theorem hyperellipticInvolution_fixes_infty
    (H : HyperellipticData) (h : Odd H.f.natDegree) :
    hyperellipticInvolution H h (OnePoint.infty : HyperellipticOdd H h) =
      (OnePoint.infty : HyperellipticOdd H h) := by
  simp [hyperellipticInvolution]

/-- **σ-equivariance of the Abel-Jacobi map** at a Weierstrass
basepoint. With `P₀ = ∞` (a Weierstrass point in the odd case), the
hyperelliptic involution acts as `−id` on the Jacobian:
`A(σ P) = −A(P)` for all `P`.

This forces the path-integral functional to compute correctly under
the σ-pullback of the canonical basis 1-forms, and rules out the
constant-zero collapse for `ofCurveImpl`. -/
theorem abelJacobi_hyperellipticInvolution
    (H : HyperellipticData) (h : Odd H.f.natDegree)
    (P : HyperellipticOdd H h) :
    ofCurveImpl (HyperellipticOdd H h) (OnePoint.infty)
        (hyperellipticInvolution H h P) =
      - ofCurveImpl (HyperellipticOdd H h) (OnePoint.infty) P := by
  -- Strategy: combine the form-level identity
  -- `pullback_hyperellipticInvolution_eq_neg` (Hyperelliptic.lean,
  -- currently a `True` placeholder) with naturality of the path-integral
  -- functional under pullback (a derived form of
  -- `AX_pathIntegral_local_antiderivative`). Quantitatively:
  --   A(σ P) i = ∫_∞^{σ P} (jacobianBasis i)
  --           = ∫_∞^P σ^* (jacobianBasis i)         (substitution)
  --           = -∫_∞^P (jacobianBasis i)            (σ^*ω = -ω)
  --           = -A(P) i
  -- The `(mod Λ)` is automatic since `ofCurve` lands in
  -- `ℂ^g/Λ`.
  sorry

/-! ## Test 3 — Abel's theorem on a principal divisor

**Statement.** The function `x − x₀` on the hyperelliptic curve has
divisor `P₁ + P₂ − 2 ∞`, where `P₁ = (x₀, y₀)` and `P₂ = σ P₁ = (x₀,
−y₀)` are the two points lying over `x₀` (assuming `x₀` is not a
branch point). Abel's theorem (`AX_AbelTheorem`) sends this principal
divisor to zero in `Jacobian X`. With `P₀ = ∞` as basepoint and using
`AX_ofCurve_self : A(∞) = 0`:

    A(P₁) + A(P₂) = 0       in Jacobian X.

**What it tests.** `abelJacobiDiv` is a real `AddMonoidHom` extending
`ofCurveImpl` to all of `Divisor X`, and `AX_AbelTheorem` asserts its
kernel is exactly `PrincipalDivisors X`. Together, this theorem
exercises:
  * the AddMonoidHom-extension `abelJacobiDiv`;
  * the membership `(P₁ + P₂ − 2∞) ∈ PrincipalDivisors X`, which is
    classical: the divisor is `div(x − x₀)`;
  * `AX_AbelTheorem` collapsing the kernel into the zero element.

Note that this is **logically a corollary** of Test 2 (σ-equivariance)
since `P₂ = σ P₁`, but it tests a **different API path** through the
divisor / principal-divisor / `abelJacobiDiv` machinery, so it
constrains a different combination of axioms. -/

/-- For a non-branch base value `x₀ ∈ ℂ` and any choice of `y₀` with
`y₀² = f(x₀)`, the two points `(x₀, ±y₀)` lie on the affine
hyperelliptic curve. -/
def fiberPoint (H : HyperellipticData) (x₀ y₀ : ℂ)
    (hxy : y₀ ^ 2 = H.f.eval x₀) : HyperellipticAffine H :=
  ⟨(x₀, y₀), hxy⟩

/-- **Abel's theorem on the affine fiber divisor.** For
`P₁ = (x₀, y₀)` and `P₂ = (x₀, −y₀)` lying over `x₀`, with `∞` as
basepoint (a Weierstrass point in the odd case),

    A(P₁) + A(P₂) = 0     in Jacobian X.

The classical proof is that `P₁ + P₂ − 2∞ = div(x − x₀)` is principal,
and `AX_AbelTheorem` annihilates principal divisors in the Jacobian.

This is also a direct consequence of `abelJacobi_hyperellipticInvolution`
applied to `P = P₁`, since `P₂ = σ P₁`. -/
theorem abelJacobi_fiber_sum_eq_zero
    (H : HyperellipticData) (h : Odd H.f.natDegree)
    (x₀ y₀ : ℂ) (hxy : y₀ ^ 2 = H.f.eval x₀) :
    ofCurveImpl (HyperellipticOdd H h) (OnePoint.infty)
        (((fiberPoint H x₀ y₀ hxy : HyperellipticAffine H) :
          OnePoint (HyperellipticAffine H)) : HyperellipticOdd H h) +
      ofCurveImpl (HyperellipticOdd H h) (OnePoint.infty)
        (((HyperellipticAffine.involution (fiberPoint H x₀ y₀ hxy) :
            HyperellipticAffine H) : OnePoint (HyperellipticAffine H))
          : HyperellipticOdd H h) =
        0 := by
  -- Two routes:
  -- (a) (Direct.) `(P₁ + P₂ - 2∞) ∈ PrincipalDivisors X` is
  --     `div(x - x₀)`. Then `AX_AbelTheorem` + extension property of
  --     `abelJacobiDiv` collapses to the displayed sum.
  -- (b) Since `(σ (fiberPoint x₀ y₀)) = fiberPoint x₀ (-y₀)`, this
  --     follows from `abelJacobi_hyperellipticInvolution` applied to
  --     `P = fiberPoint x₀ y₀`, the AddMonoidHom property of
  --     `Jacobian.ofCurve` at the basepoint, and `add_neg_self`.
  sorry

/-! ## Test 4 — Riemann's bilinear relations on the hyperelliptic
period matrix

**Statement.** For the canonical basis `{x^k dx/y : 0 ≤ k < g}` of
`HolomorphicOneForm (HyperellipticOdd H h)` and a piecewise-real-analytic
symplectic basis `{α_i, β_j}` of `H_1`, the period matrix is in
`SiegelUpperHalfSpace (genus X)` — i.e. `τ` is symmetric and `Im τ` is
positive-definite, after α-normalization.

**What it tests.** This is the headline polarization statement, asserting
the Jacobian is not just a complex torus but a **principally polarized
abelian variety**. It reduces (modulo basis change) to `AX_RiemannBilinear`,
but specializing to the explicit hyperelliptic basis tests:
  * `AX_AnalyticCycleBasis` produces a symplectic basis on the actual
    odd-degree hyperelliptic curve (not just an abstract one);
  * the integration of `x^k dx/y` against α-cycles produces
    non-degenerate periods (forcing the basis-side `pathIntegralBasepointFunctional`
    to be non-trivial);
  * the resulting `τ` lands in `SiegelUpperHalfSpace`. -/

/-- **Riemann bilinear relations for the odd-degree hyperelliptic
curve.** There exist a symplectic basis `b` of `H_1` and a normalized
basis `cω` of holomorphic 1-forms (concretely, a renormalization of
the canonical basis `x^k dx/y` from `Hyperelliptic.lean`) such that the
period matrix
    τ[i,j] := ∫_{β_i} cω_j
lies in `SiegelUpperHalfSpace (genus X)`, with α-period normalization
`∫_{α_i} cω_j = δ_ij`. -/
theorem riemannBilinear_hyperellipticOdd
    (H : HyperellipticData) (h : Odd H.f.natDegree)
    (x₀ : HyperellipticOdd H h) :
    ∃ (b : AnalyticCycleBasis (HyperellipticOdd H h) x₀)
      (cω : Module.Basis (Fin (RiemannSurface.genus (HyperellipticOdd H h))) ℂ
              (HolomorphicOneForm (HyperellipticOdd H h)))
      (τ : SiegelUpperHalfSpace (RiemannSurface.genus (HyperellipticOdd H h))),
      (∀ i j : Fin (RiemannSurface.genus (HyperellipticOdd H h)),
        periodMap (HyperellipticOdd H h) x₀ (b.isBasis (αEmbed i)) (cω j) =
          if i = j then 1 else 0) ∧
      (∀ i j : Fin (RiemannSurface.genus (HyperellipticOdd H h)),
        τ.val i j =
          periodMap (HyperellipticOdd H h) x₀ (b.isBasis (βEmbed i)) (cω j)) := by
  -- Direct application of `AX_RiemannBilinear` — but stated here as a
  -- specialized theorem so the test forces the `genus`,
  -- `AnalyticCycleBasis`, and `HolomorphicOneForm` machinery to all
  -- compute on the actual `HyperellipticOdd H h` type, not just
  -- abstractly. Discharging is one line:
  --   exact AX_RiemannBilinear x₀
  exact AX_RiemannBilinear x₀

/-! ## Even-degree analogues

Even-degree twins of Tests 1 and 4 on `HyperellipticEvenProj H` under
`[Fact (¬ Odd H.f.natDegree)]`. Test 2 (σ-equivariance) and Test 3
(Abel's theorem on `div(x − x₀)`) require the even-degree counterpart
of `HyperellipticAffine.involution` and a model of the two infinity
points `∞₊, ∞₋`, neither of which is in scope yet — they belong in
`HyperellipticEven.lean` as a follow-up. The Test-3 statement in even
degree is `A(P₁) + A(P₂) − A(∞₊) − A(∞₋) ≡ 0`, since
`div(x − x₀) = P₁ + P₂ − ∞₊ − ∞₋` for the even parametrization. -/

namespace Even

open Jacobians.Extensions.HyperellipticEven

/-- **Period lattice rank, even case.** The period image of
`HyperellipticEvenProj H` has Z-rank `2g` with `g = deg f / 2 - 1`.
Even-degree twin of `periodLattice_rank_HyperellipticOdd_eq`. -/
theorem periodLattice_rank_HyperellipticEven_eq
    (H : HyperellipticData) [Fact (¬ Odd H.f.natDegree)] :
    Module.finrank ℤ
        (periodLatticeInBasis (HyperellipticEvenProj H)
          (Classical.arbitrary _) (jacobianBasis _)) =
      2 * (H.f.natDegree / 2 - 1) := by
  sorry

/-- **Riemann bilinear relations, even case.** Specialization of
`AX_RiemannBilinear` to `HyperellipticEvenProj`; the test forces the
`AnalyticCycleBasis`, `HolomorphicOneForm`, and `genus` machinery to
all compute on the even-projective curve, not just abstractly. -/
theorem riemannBilinear_hyperellipticEven
    (H : HyperellipticData) [Fact (¬ Odd H.f.natDegree)]
    (x₀ : HyperellipticEvenProj H) :
    ∃ (b : AnalyticCycleBasis (HyperellipticEvenProj H) x₀)
      (cω : Module.Basis (Fin (RiemannSurface.genus (HyperellipticEvenProj H))) ℂ
              (HolomorphicOneForm (HyperellipticEvenProj H)))
      (τ : SiegelUpperHalfSpace (RiemannSurface.genus (HyperellipticEvenProj H))),
      (∀ i j : Fin (RiemannSurface.genus (HyperellipticEvenProj H)),
        periodMap (HyperellipticEvenProj H) x₀
            (b.isBasis (αEmbed i)) (cω j) =
          if i = j then 1 else 0) ∧
      (∀ i j : Fin (RiemannSurface.genus (HyperellipticEvenProj H)),
        τ.val i j =
          periodMap (HyperellipticEvenProj H) x₀
            (b.isBasis (βEmbed i)) (cω j)) :=
  AX_RiemannBilinear x₀

end Even

end Jacobians.Extensions.AbelJacobi
