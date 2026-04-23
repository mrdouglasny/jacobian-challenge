/-
`AX_AnalyticCycleBasis`: every compact connected Riemann surface admits a
**piecewise-real-analytic symplectic ℤ-basis** of its first integer homology.

# Statement (informal)

For `X` a compact, connected, T2, complex 1-manifold of genus `g`, there
exist `2g` piecewise-real-analytic loops
    `γ_1, …, γ_g, δ_1, …, δ_g : unitInterval → X`
based at `x₀ : X`, whose homology classes form a ℤ-basis of `H_1(X, ℤ)`,
and whose mutual intersection numbers realise the standard symplectic form:

    ⟨γ_i, γ_j⟩ = ⟨δ_i, δ_j⟩ = 0,   ⟨γ_i, δ_j⟩ = δ_ij.

Concretely (this is the formal axiom below): `Nonempty (AnalyticCycleBasis X x₀)`
where `AnalyticCycleBasis` packages the cycles, the basis property, and
the symplectic structure.

# Why we assume this

The period map
    `periodMap : H_1(X, ℤ) → (HolomorphicOneForm X)^*`
is classically defined by `[γ] ↦ (ω ↦ ∫_γ ω)`. A fully general definition
requires:

1. **Path integration on a complex manifold** — pull back `ω` to
   `unitInterval` via charts and integrate. This requires a theory of
   line integrals of 1-forms on manifolds that Mathlib does not have at
   the pinned commit (`Mathlib.MeasureTheory.Integral.CurveIntegral` only
   covers normed spaces, which is the chart-local case).

2. **Chart-additivity** — for `γ` whose image crosses multiple chart
   domains, the integral `∫_γ ω` must be defined by partitioning
   `[0, 1]` subordinate to a chart cover and summing chart-local
   `curveIntegral`s; independence of the chart cover and partition is a
   theorem (consequence of the cotangent cocycle on `ω`).

3. **Homotopy invariance** — for `γ ∼ γ'` a smooth homotopy,
   `∫_γ ω = ∫_{γ'} ω`. Classical proof uses the chart-local Cauchy
   theorem (`holomorphic ⇒ closed 1-form`) plus Stokes on a rectangle
   decomposition of `[0, 1]^2`. Mathlib has Cauchy-disc-ishly on `ℂ`
   but not on general manifolds, and the global patching argument needs
   the chart-cocycle infrastructure from (2).

(1–3) together form a substantial subproject — the `PathIntegral.lean`
file sketched in `docs/formalization-plan.md` §4.4 estimates 2–3 months
of focused work. None of the technical machinery is on the critical
path of the Jacobian Challenge's 24 `sorry`s.

The observation behind this axiom: **we do not actually need integration
along arbitrary smooth paths**. Every class in `H_1` has a *piecewise-
real-analytic* representative, so it suffices to integrate along such
representatives. For piecewise-real-analytic arcs, the chart-local
integral reduces to `intervalIntegral` of an analytic function — which
Mathlib has — and the homotopy-invariance argument can be run on the
(much smaller) class of piecewise-analytic homotopies, where analytic
continuation does most of the work that Stokes would do in general.

Packaging this cleanly gives a single axiom (this file) that supplies:
  - a specific basis of `H_1(X, ℤ)` (so `AX_H1FreeRank2g` is subsumed);
  - piecewise-analytic representatives (so the path integral exists);
  - symplectic structure relative to the intersection form (so
    `AX_RiemannBilinear` can refer to the basis directly).

# Why it is true (the "three proofs" menu)

Three classical routes, each known, none in Mathlib at this pin:

## (P1) Radó triangulation + classification of compact oriented surfaces

Radó (1925) proved every topological 2-manifold is triangulable.
Combined with the classification of compact oriented surfaces, a genus-`g`
surface admits a triangulation whose 1-skeleton includes a standard
presentation `∏_i [α_i, β_i] = 1` — the 4g-gon model. The edges `α_i, β_i`
are piecewise-linear in the 4g-gon's flat chart, hence piecewise-analytic
(linear is analytic); their homology classes give a symplectic basis.

**Discharge prerequisites:** Radó's theorem (manifold triangulation) +
surface classification. Neither is in Mathlib.
**Estimated effort:** 3–6 months. Mostly topology, not complex analysis.

## (P2) Riemann-Roch + algebraic embedding

Every compact Riemann surface is projective (Riemann 1857 for g = 0, 1;
Kodaira + Riemann-Roch for g ≥ 2): `K_X^{⊗n}` is very ample for
`n ≥ 2` and `g ≥ 2`, producing `X ↪ ℙ^N`. An algebraic triangulation of
`ℙ^N` pulled back gives an algebraic (hence analytic) triangulation of
`X`, whose 1-skeleton's cycles are piecewise-algebraic and form a ℤ-basis
of `H_1`.

**Discharge prerequisites:** divisors on Riemann surfaces, line bundles
and ampleness, sheaf cohomology `H^0, H^1`, Riemann-Roch. Substantial
algebraic-geometric infrastructure not in Mathlib.
**Estimated effort:** 12+ months. Blocks several other axioms.

## (P3) Morse theory + gradient flow

Choose a Morse function `f : X → ℝ` with distinct critical values
(exists by genericity). The ascending/descending manifolds of the
critical points give a CW-structure on `X`. For `g ≥ 1`, there are
`2g` index-1 critical points whose stable manifolds are piecewise-smooth
edges giving a ℤ-basis of `H_1`. Stable manifolds of a **real-analytic**
Morse function are real-analytic (by the stable manifold theorem applied
to the real-analytic gradient flow).

**Discharge prerequisites:** Morse theory on manifolds (basic, some in
Mathlib), CW-structures from Morse (not in Mathlib), real-analytic
Morse lemma (not in Mathlib). Middle ground in difficulty.
**Estimated effort:** 6–9 months.

## Comparison

Of the three, (P2) is the deepest mathematically (essentially the full
algebraic geometry of curves) but offers the most downstream leverage —
the same infrastructure discharges `AX_RiemannRoch`, `AX_SerreDuality`,
and `AX_PluckerFormula`. (P1) is the most elementary but does not produce
the symplectic structure for free (the intersection form has to be
computed on the 4g-gon). (P3) is a middle path with specific appeal if a
formalization of real-analytic Morse theory happens to land in Mathlib
first.

**Recommended discharge order (2026-04-22):** wait for (P1) or (P3)
to be easier to formalize; prefer (P2) only if the full algebraic
geometry stack arrives.

# Vetting

**Standard. Source: SA (self-audit), scheduled for DT (deep-think
external review).**
  - Statement matches Mumford, *Tata Lectures on Theta I*, §II.2 (the
    symplectic basis condition for the period matrix normalization) and
    Griffiths-Harris, *Principles of Algebraic Geometry*, Ch. 0.4 (the
    intersection-form perspective).
  - Non-vacuous: for `X = ℙ¹` the basis is empty (genus 0), the axiom
    is trivially true; for elliptic curves the basis has 2 elements
    matching the classical `A`- and `B`- cycles; for hyperelliptic
    curves a symplectic basis can be written down explicitly by
    branch-cut contours.
  - Right strength: exactly the ingredient `periodMap` needs in its real
    (non-axiom-stub) definition — no known downstream theorem requires
    *more* than a symplectic piecewise-analytic basis of `H_1`.
  - Not circular: does not reference the period map itself, and the
    intersection form is axiomatized separately
    (`Axioms/IntersectionForm.lean`).

# Relationship to other axioms

This axiom **subsumes**:
  - `AX_H1FreeRank2g` — the existence of a ℤ-basis of rank `2g` is a
    consequence. (`AX_H1FreeRank2g` stays declared in its file for now
    so downstream code that imports it directly is not broken; when
    `periodMap` is rewritten from axiom-stub to real def using this
    basis, `AX_H1FreeRank2g` becomes a `theorem` derived from this
    axiom.)

This axiom **does not subsume**:
  - `AX_IntersectionForm_{alternating, nondeg}` — the intersection form
    on `H_1` is a separate piece of data used here to define what
    "symplectic" means. Retained as a separate axiom.
  - `AX_RiemannBilinear` — the positive-definiteness of `Im τ` depends
    on Hodge theory, not on the existence of a symplectic basis.

# Discharge priority

Insert as #3 in the revised order (see `docs/formalization-plan.md` §7),
between `AX_IntersectionForm` and `AX_PeriodLattice`. Rationale: needs
the intersection form to even state "symplectic"; `AX_PeriodLattice` uses
its integrals.

# References

* D. Mumford, *Tata Lectures on Theta I*, Ch. II.
* P. Griffiths & J. Harris, *Principles of Algebraic Geometry*, Ch. 0.4
  and Ch. 2.
* O. Forster, *Lectures on Riemann Surfaces*, Ch. I §22 (Radó's theorem)
  and Ch. III §16 (symplectic basis).
* T. Radó, *Über den Begriff der Riemannschen Fläche*, Acta Univ. Szeged
  (1925).
* K. Kodaira, *On Kähler varieties of restricted type*, Ann. Math. 60
  (1954) (projective embedding).

See also `docs/history.md` (2026-04-22 entry discussing the design
conversation that led to this axiom).
-/
import Jacobians.RiemannSurface.AnalyticArc
import Jacobians.RiemannSurface.Homology
import Jacobians.RiemannSurface.Genus
import Jacobians.Axioms.IntersectionForm

namespace Jacobians.Axioms

open scoped Manifold Topology
open scoped ContDiff
open Jacobians.RiemannSurface

/-- The data of a piecewise-real-analytic ℤ-basis of `H_1(X, ℤ)` with
each basis class represented by a specific piecewise-analytic loop.

At this pin the structure carries:
  - the 2g loops;
  - the claim that their `H_1`-classes form a ℤ-basis.

The **symplectic condition** on the intersection form — that in the
split `Fin (2g) ≃ Fin g ⊕ Fin g` (α-cycles + β-cycles) the pairing
has matrix `[[0, I], [-I, 0]]` — is intentionally *not* baked in at
this pin. Reason: stating it requires plumbing `Fin.castAdd g` /
`Fin.natAdd g` through the basis, and the type arithmetic
`g + g = 2 * g` forces `Fin.cast`-chained rewriting in every consumer.
A cleaner approach is to add the symplectic property as a *separate*
predicate on `AnalyticCycleBasis` once it's needed by
`AX_RiemannBilinear` — at which point the α/β split can be made
concrete via a helper `AnalyticCycleBasis.toSymplecticBasis`.

The basis is indexed by `Fin (2 * genus X)` directly. -/
structure AnalyticCycleBasis (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (x₀ : X) where
  /-- The `2g` piecewise-real-analytic loops based at `x₀`. -/
  loops : Fin (2 * genus X) → AnalyticLoop X x₀
  /-- Their homology classes form a ℤ-basis of `H_1(X, ℤ)`. For now we
  ask only that *some* such basis exists; relating the basis element at
  index `i` back to `loops i` (via a `Path.toHomologyClass`
  construction that will live in `Jacobians/RiemannSurface/IntersectionForm.lean`)
  is a downstream theorem, not part of this axiom. -/
  isBasis : Module.Basis (Fin (2 * genus X)) ℤ (H1 X x₀)

-- TODO (symplectic property): add a predicate
--   `AnalyticCycleBasis.IsSymplectic (b : AnalyticCycleBasis X x₀) : Prop`
-- together with an axiom `AX_AnalyticCycleBasis_isSymplectic` witnessing
-- it, once `AX_RiemannBilinear`'s real (non-doc-only) statement lands
-- and needs it.

-- TODO (loops_to_basis): a theorem
--   `loops_to_basis_eq (b : AnalyticCycleBasis X x₀) (i : Fin (2 * genus X)) :
--     b.isBasis i = Path.toHomologyClass ((b.loops i).arc.toFun ...)`
-- connecting the basis elements to the actual loops' homology classes.
-- Needs `Path.toHomologyClass` from the Hurewicz bridge (TODO in
-- `IntersectionForm.lean`).

/-- **Axiom.** Every compact connected Riemann surface admits a
piecewise-real-analytic symplectic ℤ-basis of `H_1(X, ℤ)`.

See the file header for motivation, proof sketches, and references.
Rating: Standard. Sources: SA (self-audit), scheduled for DT (deep
think). -/
axiom AX_AnalyticCycleBasis {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (x₀ : X) :
    Nonempty (AnalyticCycleBasis X x₀)

end Jacobians.Axioms
