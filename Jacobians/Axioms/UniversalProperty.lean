import Jacobians.Challenge

/-!
# Axioms for the Jacobian universal property

Deferred textbook leaves of the universal-property discharge plan
(`docs/universal-property-proof-plan.md`), proving
`Jacobians.IsJacobian x₀ (Jacobian X) (ofCurve x₀)`.

Only the **uniqueness** axiom (`AX_curve_generates_jacobian`) is statable as a
standalone fact over the existing API. The three *existence/factorization* axioms
(`AX_torus_oneforms_dualCover`, `AX_torus_self_albanese`, `AX_period_functoriality`)
quantify over the internal cover/lattice scaffolding of a complex torus that this
repo does not yet have as standalone objects; they are recorded in
`AXIOM_AUDIT.md` and the proof plan, to be stated once that scaffolding lands.

All four were cross-model vetted (Gemini gemini-3-pro-preview + Codex, 2026-06-02).
-/

open scoped Manifold ContDiff

namespace Jacobians.Axioms

/-- **Axiom (a curve generates its Jacobian).** For a compact Riemann surface `X`
of positive genus with basepoint `x₀`, the image of the Abel–Jacobi map generates
the Jacobian as a group:
`AddSubgroup.closure (Set.range (ofCurve x₀)) = ⊤`.

This is the **uniqueness** half of the Jacobian universal property: two group
homomorphisms out of `Jac X` that agree on `aj(X)` agree on the whole generated
subgroup, hence everywhere. Part of the classical Abel–Jacobi theorem; `0 < genus X`
is essential (for genus 0 the Jacobian is a point and the statement is vacuous).

Reference: Mumford, *Curves and their Jacobians*; Milne, *Abelian Varieties* §I.
Strategy: Jacobi inversion — every element of `Jac X` is a difference of effective
divisors of degree `g`, i.e. a sum of `g` Abel–Jacobi images minus `g·aj(x₀)`; so
the `g`-fold sumset of `aj(X)` already covers `Jac X`.

Vetting: cross-model **Gemini** (gemini-3-pro-preview) + **Codex**, 2026-06-02 —
correct, non-vacuous, `0 < genus X` necessary; algebraic generation (vs. topological)
is the standard, stronger, and easier-to-use form; Codex confirmed Mathlib has no
Jacobian-of-a-curve / Jacobi-inversion API (genuinely absent). (NOT VERIFIED — the
formal proof is deferred; this is textbook debt on the path to 0 axioms.) -/
axiom AX_curve_generates_jacobian {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (x₀ : X) (h : 0 < genus X) :
    AddSubgroup.closure (Set.range (Jacobian.ofCurve x₀)) = ⊤

end Jacobians.Axioms
