# Design — Jacobians Lean API

Long-term design choices for the Jacobians API challenge. Companion to
`recon.md` (mathlib availability audit) and `REFERENCES.md` (textbook
pointers).

## Optimization axes

Three axes, listed in priority order:

1. **Chance of success.** Curve-only by default. Don't detour through
   Albanese / compact Kähler / Picard scheme / GAGA. Avoid constructions
   that require new theory simply to *state* the definition.
2. **Mathlib fit.** Every new piece should live naturally in a Mathlib
   file and follow Mathlib style: bundled types, `@[simp]` API surfaces,
   minimal instance argument lists, `irreducible` main defs after the API
   stabilizes, split heavy instances into sibling files.
3. **Cheap generalization.** When building a piece in the broadest natural
   setting is *essentially the same effort* as building it for the curve
   case, build it in the broader setting. When generalization drags in new
   theory (Hodge, higher-dim period lattices, sheaf cohomology of analytic
   spaces), stay curve-only and flag the generalization as future work.

## Canonical definitions

### `genus`

```
genus X : ℕ := finrank ℤ (H₁(X, ℤ)) / 2     -- closed oriented 2-manifold
```

Build at the topological level: closed oriented 2-manifolds. For a compact
Riemann surface this specializes trivially since it's a closed oriented
2-manifold. Equality with `dim_ℂ H⁰(X, Ω¹_X)` is a theorem (the analytic
side of Riemann-Roch / Dolbeault for curves).

Alternative to consider during build: `(2 - χ(X)) / 2` via
`HomologicalComplex.eulerChar` on the singular chain complex (the Euler
char infrastructure is already in Mathlib). Whichever is cheapest to work
with in practice.

### `Jacobian`

```
Jacobian X := (H⁰(X, Ω¹_X))ᵛ ⧸ (image of H₁(X, ℤ) under period pairing)
```

Curve-only. The Albanese of a compact Kähler manifold is deferred (see
*Future work*). The period pairing

```
H₁(X, ℤ) × H⁰(X, Ω¹_X) → ℂ,  (γ, ω) ↦ ∫_γ ω
```

gives a ℤ-linear map `H₁(X, ℤ) → (H⁰(X, Ω¹_X))ᵛ` whose image is an
`IsZLattice ℝ _` inside the underlying real vector space. The quotient is a
compact complex Lie group of dimension `genus X` by standard arguments.

**Encoding plan (elaboration-aware):**

- Define `periodLattice X : Submodule ℤ (…)ᵛ` as a named `Submodule ℤ`
  inside the real-underlying space of the dual.
- Define `Jacobian X` as a wrapper `def` (not `abbrev`, not `structure`)
  around `(H⁰(X, Ω¹_X))ᵛ ⧸ AddSubgroup.closure (periodLattice X)` so
  downstream files don't pattern-match on the representation.
- Mark `Jacobian` `irreducible` (via `irreducible_def` or equivalent) once
  the API is complete.
- Provide `Jacobian.mk`, `Jacobian.lift`, `@[simp] lemma mk_zero`,
  `mk_add`, `lift_mk`, `ofCurve_apply`, etc.

### `ofCurve` (Abel–Jacobi map)

```
ofCurve P (Q : X) : Jacobian X := Jacobian.mk (fun ω ↦ ∫_{γ : P ⇝ Q} ω)
```

where the path integral is interpreted mod `periodLattice` so the value is
independent of the path. Well-definedness requires either the universal
cover story or the simply-connected-path-class quotient from `π₁`.

### `pushforward` and `pullback`

Curve-only. For `f : X → Y` holomorphic:

```
pushforward f hf : Jacobian X →ₜ+ Jacobian Y
  = descent of (H⁰(X, Ω¹)ᵛ → H⁰(Y, Ω¹)ᵛ) induced by pushforward on cycles / forms

pullback f hf : Jacobian Y →ₜ+ Jacobian X
  = descent of (H⁰(Y, Ω¹)ᵛ → H⁰(X, Ω¹)ᵛ) induced by pullback of forms
```

API: provide `pushforward_apply`, `pullback_apply`, `pushforward_id`,
`pushforward_comp`; mirror for `pullback`. These should typecheck without
unfolding `Jacobian`.

### `ContMDiff.degree`

Natural `ℕ` assigned to a holomorphic map `f : X → Y` between compact
Riemann surfaces; 0 iff `f` is constant, else the usual degree (cardinality
of a generic fibre = degree of `f^{-1}(P)` as a divisor).

**Cheap generalization:** define `degree` for a proper holomorphic map
between equidim connected complex manifolds, then specialize. The
definition is the same; it lives naturally in
`Mathlib/Geometry/Manifold/Complex.lean` or a sibling.

## Dependency graph

```
              ┌─── Mathlib: singular H₁, IsZLattice, LieAddGroup, …
              │
              ▼
┌───────────────────────────────────────┐
│ genus (topological)                    │── closed oriented 2-manifolds
└───────────────────────────────────────┘
              │
              ▼
┌───────────────────────────────────────┐
│ holomorphic 1-forms  H⁰(X, Ω¹_X)        │── any complex manifold (cheap gen.)
└───────────────────────────────────────┘
              │
              ▼
┌───────────────────────────────────────┐
│ path integral ∫_γ ω on a manifold       │── smooth manifold (cheap gen.)
└───────────────────────────────────────┘
              │
              ▼
┌───────────────────────────────────────┐
│ period pairing → IsZLattice image       │── curve-only
└───────────────────────────────────────┘
              │
              ▼
┌───────────────────────────────────────┐    ┌──────────────────────────────┐
│ Quotient Lie group  E ⧸ Λ               │    │ degree of proper holom. map │
│ (E f.d. normed, Λ IsZLattice)           │    │ (equidim complex manifolds) │
└───────────────────────────────────────┘    └──────────────────────────────┘
              │                                          │
              ├──────────────────────┬──────────────────┘
              ▼                      ▼
┌───────────────────────────────────────┐
│ Jacobian X (all instances 65–86)        │
└───────────────────────────────────────┘
              │
              ├────► ofCurve, ofCurve_contMDiff, ofCurve_self
              │         │
              │         ▼
              │    ofCurve_inj (Abel's theorem)                  ← headline
              │
              ├────► pushforward / pullback + functoriality
              │         │
              │         ▼
              │    pushforward_pullback (= degree)                ← headline
              │
              └────► genus_eq_zero_iff_homeo                      ← headline
                        (needs uniformization for genus 0)
```

Three "headline" sorries at the leaves: each is a classical theorem that
requires substantial content; the rest are structural.

## Proposed Mathlib file layout

When these contributions are ready to upstream:

| New / modified Mathlib file | Content |
|---|---|
| `Mathlib/Algebra/Module/ZLattice/Quotient.lean` (new) | `IsZLattice` quotient is a Lie group; `CompactSpace`, `T2`, `ChartedSpace`, `IsManifold`, `LieAddGroup` instances on `E ⧸ Λ` |
| `Mathlib/Geometry/Manifold/DifferentialForm/Basic.lean` (new) | Bundled smooth `n`-forms on a manifold (`d` of a form, pullback by a smooth map) |
| `Mathlib/Geometry/Manifold/Complex/OneForm.lean` (new) | Holomorphic 1-forms on a complex manifold; global sections as a ℂ-module; finite-dimensionality on compact manifolds of dim 1 |
| `Mathlib/Analysis/Calculus/LineIntegral.lean` (new) | Line integral of a 1-form along a smooth path on a manifold |
| `Mathlib/Geometry/Manifold/Complex/Degree.lean` (new) | Degree of a proper holomorphic map between equidim connected complex manifolds |
| `Mathlib/Topology/AlgebraicTopology/Hurewicz.lean` (new) | `π₁(X,x₀)ᵃᵇ ≃ H₁(X, ℤ)` (medium gap) |
| `Mathlib/Geometry/RiemannSurface/Basic.lean` (new) | `genus`, `ofCurve`, `Jacobian`, pushforward/pullback, Abel's theorem |

Curve-specific material lives under `Mathlib/Geometry/RiemannSurface/`;
everything above that line is reusable Mathlib theory.

## API style rules (elaboration + ergonomics)

- Public API surfaces `Jacobian.mk`, `Jacobian.lift`, not the
  `QuotientAddGroup` representation. Users never see the underlying dual
  or the lattice.
- Provide `@[simp]` lemmas: `mk_zero`, `mk_add`, `mk_neg`,
  `lift_mk`, `mk_eq_mk_iff`, `ofCurve_self`, `pushforward_apply`,
  `pushforward_zero`, `pushforward_add`, mirror for `pullback`.
- Use `def Jacobian … := …` (not `abbrev`), mark `irreducible` after API.
- Typeclass instances split across files: one file per instance cluster so
  downstream elaboration only pays for what it imports.
- Keep `ContMDiff.degree` as `_root_.ContMDiff.degree` per the challenge
  file; all other APIs namespaced under `Jacobian.`.
- Follow the manifold file's existing conventions on `{𝕜 : Type*}`
  argument ordering, `{n : WithTop ℕ∞}` placement, etc.

## Future work (explicitly deferred)

- **Albanese variety** for compact Kähler manifolds of any complex
  dimension. `Jacobian X := Albanese X` for dim 1 as a definitional
  equivalence.
- **Pic⁰ / GAGA** — the algebraic definition of the Jacobian via divisor
  classes of degree 0 and the canonical iso with the analytic Jacobian.
- **Intermediate Jacobians** (higher-dim Kähler).
- **Riemann–Roch for curves**, **Serre duality**, **Hodge decomposition**
  — all will come naturally as downstream consequences once the analytic
  infrastructure matures.

Deferring these does not preclude upstreaming: the pieces we *do* build
(quotient Lie groups by ZLattices, holomorphic 1-forms, line integrals,
degree of a proper holomorphic map, Hurewicz) are exactly the building
blocks a future Albanese formalization will need.
