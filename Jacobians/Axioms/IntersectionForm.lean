/-
`AX_IntersectionForm`: the integer-valued intersection pairing on
`H_1(X, ℤ)` for a compact oriented surface.

**Statement.** For `X` a compact Riemann surface, there is a non-degenerate
alternating ℤ-bilinear pairing

    ⟨·, ·⟩ : H₁(X, ℤ) × H₁(X, ℤ) → ℤ

called the *intersection form*, geometrically counting (with signs) the
oriented transverse intersections of representatives of two homology
classes.

**Why true.** Poincaré duality for a compact oriented 2-manifold gives
`H₁(X, ℤ) ≅ H¹(X, ℤ)`, and the cup product

    H¹(X, ℤ) × H¹(X, ℤ) → H²(X, ℤ) ≅ ℤ

transported through the iso is the intersection form. Non-degeneracy of
Poincaré duality gives non-degeneracy of the form; the cup product is
graded-commutative so on odd degrees it's alternating.

**Why axiomatized.** Poincaré duality + cup product on a compact oriented
surface is a chunk of algebraic topology not in Mathlib at the pin. It
could be replaced by a direct CW-based proof using the surface's
`∏ [α_i, β_i] = 1`-presentation, which is also not in Mathlib.

**Consequences.**
* Gives formal meaning to "symplectic basis of `H_1`" — a ℤ-basis in which
  the intersection form has matrix `[[0, I], [-I, 0]]`. The existence of
  such a basis is a standard consequence of the classification of
  alternating forms over ℤ (or over a PID — both are in Mathlib, so given
  `AX_IntersectionForm` we can derive symplectic bases as a theorem).
* Required to state `AX_RiemannBilinear` (the normal form `[I | τ]` of the
  period matrix is defined relative to a *symplectic* basis of `H_1`).

**Axiom-stub pattern.** Following the `periodMap` precedent, we declare
the pairing itself as an `axiom` (a typed stub), alongside its
characterizing property axioms. When CW-homology lands and we can
actually construct the pairing from topology, these axioms retire to
theorems.

See `docs/formalization-plan.md` §7; discharge priority #3 in the revised
ordering. Reference: Mumford Vol I §II.1; Hatcher §3.3; Griffiths-Harris
Ch. 0.4.
-/
import Jacobians.RiemannSurface.Homology

namespace Jacobians.Axioms

open scoped Manifold Topology
open scoped ContDiff
open Jacobians.RiemannSurface

/-- **Axiom-stub.** The intersection pairing on `H_1(X, ℤ)` for a compact
Riemann surface, as a ℤ-bilinear form (i.e. a ℤ-linear map into its own
dual). Replaced by a real definition when CW homology + Poincaré duality
become available. -/
axiom intersectionForm {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (x₀ : X) :
    H1 X x₀ →+ (H1 X x₀ →+ ℤ)

/-- **Axiom.** The intersection form is alternating: `⟨a, a⟩ = 0` for all
`a ∈ H_1(X, ℤ)`. -/
axiom AX_IntersectionForm_alternating
    {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (x₀ : X) (a : H1 X x₀) :
    intersectionForm x₀ a a = 0

/-- **Axiom.** The intersection form is a **perfect pairing** — i.e. a
ℤ-module isomorphism between `H_1(X, ℤ)` and its ℤ-dual. This is the
**unimodularity** of the pairing, a consequence of Poincaré duality on
a compact oriented surface.

Perfect pairing is strictly stronger than non-degeneracy over ℤ:
injectivity alone (the classical "non-degeneracy") says
`⟨a, _⟩ = 0 ⟹ a = 0`, but unimodularity additionally says every
ℤ-linear functional `φ : H_1 →+ ℤ` is of the form `⟨a, _⟩` for some
unique `a`. Without surjectivity, one cannot extract a **symplectic
basis over ℤ** that brings the period matrix to standard `[I | τ]`
block form.

Per Gemini review #2 (2026-04-23, `docs/gemini-review-axioms-2.md`),
the weaker `AX_IntersectionForm_nondeg` is upgraded to this
`Function.Bijective` form.

Injectivity as a consequence is recorded as
`AX_IntersectionForm_nondeg` (theorem below). -/
axiom AX_IntersectionForm_perfect
    {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (x₀ : X) :
    Function.Bijective (intersectionForm x₀)

/-- **Theorem** (derived from `AX_IntersectionForm_perfect`). The
intersection form is non-degenerate: if `⟨a, b⟩ = 0` for every `b`, then
`a = 0`. Kept under its original name so existing callers continue to
work. -/
theorem AX_IntersectionForm_nondeg
    {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (x₀ : X) (a : H1 X x₀)
    (h : ∀ b : H1 X x₀, intersectionForm x₀ a b = 0) :
    a = 0 := by
  have hInj := (AX_IntersectionForm_perfect x₀).1
  apply hInj
  apply AddMonoidHom.ext
  intro b
  simpa using h b

end Jacobians.Axioms
