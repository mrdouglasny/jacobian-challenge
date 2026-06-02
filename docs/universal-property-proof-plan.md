# Discharge plan — the Jacobian universal property

*Goal: prove `Jacobians.IsJacobian x₀ (Jacobian X) (Jacobian.ofCurve x₀)` —
that Buzzard's concrete Jacobian satisfies the Albanese universal property
([`Jacobians/UniversalProperty.lean`](../Jacobians/UniversalProperty.lean)). This is
the **categoricity** theorem: with it, `(Jacobian X, ofCurve)` is pinned up to
unique isomorphism, closing the def-degeneracy gap categorically. Authored
2026-06-02.*

This follows the project's **vetted-textbook-axiom deferral** methodology: classify
each leaf as already-in-repo, Mathlib-derivable, a vetted textbook axiom (deferred
debt on the path to 0 axioms), or novel glue to prove.

## Goal statement

```lean
theorem ofCurve_isJacobian {X : Type} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (x₀ : X) :
    Jacobians.IsJacobian x₀ (Jacobian X) (Jacobian.ofCurve x₀)
```

`aj_holo` and `aj_base` are **already repo theorems** (`Jacobian.ofCurve_contMDiff`,
`Jacobian.ofCurve_self`). All the work is the `universal` field.

## Step 0 — prerequisites (mechanical)

- **[done] Dimension fix.** The statement now models `J`/`A` on `Fin g → ℂ` /
  `Fin m → ℂ` (was `ℂ`, which restricted it to genus 1). Verified: every instance
  on `Jacobian X` resolves except the next item.
- **[done] `instance : ConnectedSpace (Jacobian X)`.** Added a general
  `ConnectedSpace (ULift α)` transfer (`Homeomorph.connectedSpace_iff`; Mathlib
  lacked it) + the exposure on `Jacobian X`
  (`Jacobian/Construction.lean`, `Challenge.lean`). The underlying `ComplexTorus`
  already had `ConnectedSpace`; it just wasn't surfaced through the `ULift`/opaque-
  `def` layers. Full `lake build` green.
- **[usage note] supply `g` explicitly.** The goal must be written
  `IsJacobian (g := genus X) x₀ (Jacobian X) (ofCurve x₀)` — otherwise `g` is a
  metavariable when `LieAddGroup` synthesis fires (resolution stalls before the
  `ChartedSpace (Fin g → ℂ)` instance pins it). With `(g := genus X)` the goal type
  fully elaborates against the real genus-`g` Jacobian (verified).

## The `universal` field — lemma DAG

Given a complex torus `A = W/Λ_A` (dim `m`, `W = ℂ^m`) and holomorphic `f : X → A`
with `f x₀ = 0`, produce a unique holomorphic group hom `φ : Jac X → A` with
`f = φ ∘ aj`.

### Existence of φ

| ID | Statement | Classification |
|----|-----------|----------------|
| **E1** | `f* : H⁰(A,Ω¹) → H⁰(X,Ω¹)`, pullback of holomorphic 1-forms (ℂ-linear) | **repo** — `pullbackOneForm` (`Axioms/AbelJacobiMap.lean`), Kirov `pullbackForm` |
| **E2a** | `H⁰(A,Ω¹) ≃ₗ[ℂ] W*` (invariant forms ≅ dual of the cover/Lie algebra) | **vetted axiom** `AX_torus_oneforms_dualCover` |
| **E2b** | `(W*)* ≃ₗ[ℂ] W` (canonical, finite-dim) | **Mathlib** — `Module.evalEquiv` (reflexive), *not* an axiom |
| **E3** | dual `(f*)* : H⁰(X,Ω¹)* → (H⁰(A,Ω¹))* ≃ W` | **repo + E2** — `LinearMap.dualMap` then E2a/E2b |
| **E4** | `(f*)*` maps `Λ_X = H₁(X;ℤ)` (period lattice) into `Λ_A` | **vetted axiom** `AX_period_functoriality` |
| **E5** | a ℂ-linear, lattice-compatible map descends to a **group hom** `φ : Jac X → A` on the quotient tori | **repo/Mathlib** — Kirov `ZLatticeQuotient` (quotient map a surjective local homeo) + `QuotientAddGroup` |
| **E6** | that descended group hom is **holomorphic** | **repo/Mathlib (likely provable)** — a ℂ-linear map is smooth (`LinearMap.toContinuousLinearMap`) and smoothness descends through the `ZLatticeQuotient` covering. *Fallback:* axiomatize only the **lift** form `AX_torus_descent_holo` (see note) — **not** "every abstract hom is holomorphic" (false: non-continuous group homs of tori exist; Codex-flagged) |

### Factorization `f = φ ∘ aj`

| ID | Statement | Classification |
|----|-----------|----------------|
| **F1** | `aj p = [∫_{x₀}^p (·)]` mod `Λ_X` (definitional for `ofCurve`); so `φ(aj p) = [(f*)* ∫_{x₀}^p]` | **repo** — `ofCurve` definition |
| **F2** | `(f*)*(∫_{x₀}^p ·) = ∫_{x₀}^p (f* ·) = ∫_{f∘γ} · = ∫_{0}^{f p} ·` (naturality / change of variables for line integrals) | **repo** — Kirov `pathSpeed_comp_eq_mfderiv`, `lineIntegral_pullback` |
| **F3** | on a torus, `[∫_0^a (·)] = a` (the torus is its own Albanese); with `f x₀ = 0` this gives `φ(aj p) = f p` | **vetted axiom** `AX_torus_self_albanese` |

### Uniqueness of φ

| ID | Statement | Classification |
|----|-----------|----------------|
| **U1** | for `g ≥ 1`, `aj '' X` generates `Jac X` as a group | **vetted axiom** `AX_curve_generates_jacobian` |
| **U2** | two group homs agreeing on a generating set are equal (`AddSubgroup.closure` + `AddMonoidHom.eq_of_eqOn` / `.ext`) | **repo/Mathlib** |

## The vetted textbook axioms (deferred debt)

**Cross-model vetting — Gemini (gemini-3-pro-preview) + Codex, 2026-06-02 (both
complete).** Gemini reshaped the original 3-axiom list (split the bundled torus
axiom; one sub-part is Mathlib; flagged a missing holomorphicity step). Codex then
searched Mathlib and confirmed what's importable vs. genuinely absent, and
**corrected the holomorphicity axiom as over-strong**. Net: **4 firm axioms**
(below) + 1 likely-provable step (E6) + 1 Mathlib import (double-dual). Each axiom is
cited, atomic, and stated in the `~/.claude/CLAUDE.md` format; enter in
`AXIOM_AUDIT.md`.

| Axiom | One-line | Mathlib status (Codex) | Reference |
|-------|----------|------------------------|-----------|
| `AX_torus_oneforms_dualCover` | for a complex torus `A = W/Λ`, `H⁰(A,Ω¹)` (invariant forms) `≃ₗ[ℂ] W*` | **partial** — `GroupLieAlgebra`, `addInvariantVectorField`, `extDeriv` exist; the form≅cotangent equiv is absent | Birkenhake–Lange Ch. 1 |
| `AX_torus_self_albanese` | the torus' own Abel–Jacobi `a ↦ [ω ↦ ∫₀ᵃ ω]` is an iso `A ≅ Jac A` (integrating invariant forms recovers points) | absent | Birkenhake–Lange Ch. 1 |
| `AX_period_functoriality` | a holomorphic `f : X → A` makes the dual period map send `Λ_X` into `Λ_A` (`∮_{f_*γ}ω = ∮_γ f*ω` is the *proof*; `(f*)*(Λ_X) ⊆ Λ_A` is the *statement*) | **partial** — `curveIntegral`, `singularHomologyFunctor` + homotopy-invariance exist; the period pairing + its naturality absent | Griffiths–Harris Ch. 0 & 2 |
| `AX_curve_generates_jacobian` | for genus `g ≥ 1`, `AddSubgroup.closure (Set.range (ofCurve x₀)) = ⊤` (algebraic generation — stronger than topological, true by Jacobi inversion) | **absent** (only `WeierstrassCurve.Jacobian` projective coords) | Mumford; Milne *AV* §I |

*Not axioms:* the double-dual `(W*)* ≃ W` is Mathlib `Module.evalEquiv`
(`LinearAlgebra.Dual.Lemmas`); E6's holomorphicity is likely provable (E6 row).

**Conditional fallback axiom (only if E6 isn't proved directly):**
`AX_torus_descent_holo` — *the map on quotient tori induced by a ℂ-linear,
lattice-compatible map of the universal covers is a holomorphic group hom.* Stated
as the **lift/descent** form per Codex's correction; the tempting "every abstract
group hom of tori is holomorphic" is **false** without a continuity/lift hypothesis.

**Anti-vacuity (Gemini + Codex).** `AX_curve_generates_jacobian` is the load-bearing
uniqueness pin, unsatisfiable by a degenerate `Jac` (a point fails it for `g ≥ 1`,
consistent with `ofCurve_inj`). `AX_period_functoriality` constrains the
*relationship* between two real period lattices — a placeholder lattice can't
discharge it. The torus axioms are statements about *arbitrary* complex tori,
independent of our `Jacobian`. All are standard, non-vacuous, and jointly sufficient.

## Mathlib scaffolding to import (Codex)

- **Double-dual:** `Mathlib.LinearAlgebra.Dual.Lemmas` — `Module.evalEquiv`,
  reflexivity via `Module.instIsReflexiveOfFiniteOfProjective`.
- **Invariant forms / Lie algebra:** `Geometry.Manifold.GroupLieAlgebra`
  (`addInvariantVectorField`, `contMDiff_addInvariantVectorField`),
  `Algebra.LeftInvariantDerivation`; vector-space forms `extDeriv`,
  `extDeriv_pullback` (`Analysis.Calculus.DifferentialForm.Basic`).
- **Periods / homology:** `MeasureTheory.Integral.CurveIntegral.Basic` +
  `…/Poincare.lean`; `AlgebraicTopology.SingularHomology.Basic` +
  `…/HomotopyInvariance.lean`.
- **Lattice quotient / descent:** `Algebra.Module.ZLattice.Basic`
  (`IsZLattice`, `ZSpan.fundamentalDomain`, `ZLattice.basis/rank/comap`),
  `Topology.Covering.AddCircle`, `LinearMap.toContinuousLinearMap`
  (`Topology.Algebra.Module.FiniteDimension`) — for E5/E6.

## Effort & sequencing

Sister-project calibration (the analytic infrastructure already exists —
`pullbackOneForm`, `dualMap`, Kirov line integral + `ZLatticeQuotient`): **a few
weeks to a proof modulo the 4 vetted axioms (+ the conditional fallback if E6 needs it).** Suggested order:

1. Step 0 (`ConnectedSpace` instance) — unblocks the goal type. *(hours)*
2. State the 4 axioms (Gemini + Codex vetted) + import the Mathlib scaffolding above; record in `AXIOM_AUDIT.md`. *(days)*
3. Existence E1–E5 → define `φ`. *(~1 week; E5 descent is the fiddly part)*
4. Factorization F1–F3. *(the meatiest — the change-of-variables identity F2 is the
   core; ~1 week)*
5. Uniqueness U1–U2. *(days)*
6. Assemble `ofCurve_isJacobian`; `#print axioms` should show only the standard
   three axioms ∪ the 4 vetted axioms (+ `AX_torus_descent_holo` if E6 used) ∪ the pre-existing Jacobian-construction
   axioms.

## Scope caveat

This proves the universal property **on top of** the existing Jacobian
construction. `ofCurve` and the period lattice already rest on the project's
period-lattice + path-integral axioms (e.g. the `pathIntegralBasepointFunctional`
FTC, still in flight — see README). So `ofCurve_isJacobian` is sound *relative to*
those; it does not make `ofCurve` itself more real. The categoricity payoff (pinning
up to iso) is nonetheless genuine: it shows any construction satisfying the same
axioms is canonically isomorphic to ours.

## Acceptance

`lake build` green; `#print axioms ofCurve_isJacobian` ⊆ `{propext,
Classical.choice, Quot.sound}` ∪ {the 4 vetted axioms (+ fallback if used)} ∪ {pre-existing
Jacobian-construction axioms}; no new `sorry`; the 4 axioms vetted (Gemini+Codex)
and logged in `AXIOM_AUDIT.md` with `(NOT VERIFIED)` cleared.
