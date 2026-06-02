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
- **[todo, easy] `instance : ConnectedSpace (Jacobian X)`.** A complex torus is
  connected (continuous surjective image of the connected `Fin g → ℂ` under the
  quotient map). Buzzard's API supplies `T2Space`/`CompactSpace` but not this.
  ~10–20 LOC via `ConnectedSpace` of a quotient of a connected space
  (`Quotient`/`ZLatticeQuotient` surjection). Needed for the goal to typecheck.

## The `universal` field — lemma DAG

Given a complex torus `A = W/Λ_A` (dim `m`, `W = ℂ^m`) and holomorphic `f : X → A`
with `f x₀ = 0`, produce a unique holomorphic group hom `φ : Jac X → A` with
`f = φ ∘ aj`.

### Existence of φ

| ID | Statement | Classification |
|----|-----------|----------------|
| **E1** | `f* : H⁰(A,Ω¹) → H⁰(X,Ω¹)`, pullback of holomorphic 1-forms (ℂ-linear) | **repo** — `pullbackOneForm` (`Axioms/AbelJacobiMap.lean`), Kirov `pullbackForm` |
| **E2** | `H⁰(torus,Ω¹) ≅ W*` (translation-invariant forms); integration identifies `W = H⁰(A,Ω¹)*`, with the torus' own Abel–Jacobi map the identity | **vetted axiom** `AX_torus_invariant_forms` |
| **E3** | dual `(f*)* : H⁰(X,Ω¹)* → W` | **repo** — `LinearMap.dualMap` |
| **E4** | `(f*)*` maps `Λ_X = H₁(X;ℤ)` (period lattice) into `Λ_A` | **vetted axiom** `AX_period_functoriality` |
| **E5** | a ℂ-linear, lattice-compatible map descends to a holomorphic group hom `φ : Jac X → A` on the quotient tori | **repo/Mathlib** — Kirov `ZLatticeQuotient` (quotient map a surjective local homeo) + `QuotientAddGroup` |

### Factorization `f = φ ∘ aj`

| ID | Statement | Classification |
|----|-----------|----------------|
| **F1** | `aj p = [∫_{x₀}^p (·)]` mod `Λ_X` (definitional for `ofCurve`); so `φ(aj p) = [(f*)* ∫_{x₀}^p]` | **repo** — `ofCurve` definition |
| **F2** | `(f*)*(∫_{x₀}^p ·) = ∫_{x₀}^p (f* ·) = ∫_{f∘γ} · = ∫_{0}^{f p} ·` (naturality / change of variables for line integrals) | **repo** — Kirov `pathSpeed_comp_eq_mfderiv`, `lineIntegral_pullback` |
| **F3** | on a torus, `[∫_0^a (·)] = a`; with `f x₀ = 0` this gives `φ(aj p) = f p` | from **E2** (`AX_torus_invariant_forms`) |

### Uniqueness of φ

| ID | Statement | Classification |
|----|-----------|----------------|
| **U1** | for `g ≥ 1`, `aj '' X` generates `Jac X` as a group | **vetted axiom** `AX_curve_generates_jacobian` |
| **U2** | two group homs agreeing on a generating set are equal (`AddSubgroup.closure` + `AddMonoidHom.eq_of_eqOn` / `.ext`) | **repo/Mathlib** |

## The three vetted textbook axioms (deferred debt)

Each will be stated with the format in `~/.claude/CLAUDE.md` (one-line English +
Reference + Strategy), marked `(NOT VERIFIED)` until the Gemini+Codex vetting pass,
and entered in `AXIOM_AUDIT.md`. None uses a project definition vacuously — all are
classical statements about complex tori / periods / curves.

| Axiom | One-line | Reference |
|-------|----------|-----------|
| `AX_torus_invariant_forms` | `H⁰(A,Ω¹)` for a complex torus `A = W/Λ` is the space of translation-invariant forms `≅ W*`; integrating them recovers points of `A` (the torus is its own Albanese) | Birkenhake–Lange, *Complex Abelian Varieties* 2nd ed., Ch. 1 |
| `AX_period_functoriality` | a holomorphic `f : X → A` induces `f_* : H₁(X;ℤ) → H₁(A;ℤ)` with `∮_{f_*γ} ω = ∮_γ f*ω`; hence the dual period map sends `Λ_X` into `Λ_A` | Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 & 2 |
| `AX_curve_generates_jacobian` | for a compact Riemann surface of genus `g ≥ 1`, the Abel–Jacobi image `aj '' X` generates `Jac X` as a group | Mumford, *Curves and their Jacobians*; Milne, *Abelian Varieties* §I |

**Anti-vacuity note.** `AX_curve_generates_jacobian` is the load-bearing
uniqueness pin and is *not* satisfiable by a degenerate `Jac` (a point fails it for
`g ≥ 1`, consistent with Abel injectivity `ofCurve_inj`). `AX_period_functoriality`
constrains the *relationship* between two real period lattices; it cannot be
discharged by a placeholder lattice. `AX_torus_invariant_forms` is a statement about
*arbitrary* complex tori, independent of the project's `Jacobian` construction.

## Effort & sequencing

Sister-project calibration (the analytic infrastructure already exists —
`pullbackOneForm`, `dualMap`, Kirov line integral + `ZLatticeQuotient`): **a few
weeks to a proof modulo the 3 vetted axioms.** Suggested order:

1. Step 0 (`ConnectedSpace` instance) — unblocks the goal type. *(hours)*
2. State + vet the 3 axioms; record in `AXIOM_AUDIT.md`. *(days)*
3. Existence E1–E5 → define `φ`. *(~1 week; E5 descent is the fiddly part)*
4. Factorization F1–F3. *(the meatiest — the change-of-variables identity F2 is the
   core; ~1 week)*
5. Uniqueness U1–U2. *(days)*
6. Assemble `ofCurve_isJacobian`; `#print axioms` should show only the standard
   three axioms ∪ the 3 vetted axioms ∪ the pre-existing Jacobian-construction
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
Classical.choice, Quot.sound}` ∪ {the 3 vetted axioms} ∪ {pre-existing
Jacobian-construction axioms}; no new `sorry`; the 3 axioms vetted (Gemini+Codex)
and logged in `AXIOM_AUDIT.md` with `(NOT VERIFIED)` cleared.
