# Plan

## Phase A — Get it building

1. `lake update` to pull Mathlib at the pinned commit.
2. Confirm `Jacobians/Challenge.lean` type-checks with the current sorries. Any elaboration errors (e.g. instance-resolution failures) count as bugs to report upstream to Buzzard's gist.
3. Stand up CI (`.github/workflows/lean.yml`) running `lake build` on push.

## Phase B — Survey

Before committing to a construction, audit what Mathlib at the pinned commit already supports:

- Holomorphic 1-forms on a complex manifold: search `Mathlib.Geometry.Manifold.ContMDiff.*` and `Mathlib.Analysis.Complex.*`.
- Integration along a curve on a manifold: anything beyond `Mathlib.MeasureTheory.Integral.IntervalIntegral`?
- Meromorphic functions / divisors on a Riemann surface: `Mathlib.Analysis.Meromorphic.*`, but likely nothing curve-specific.
- First singular/de Rham homology of a compact manifold: `Mathlib.AlgebraicTopology.*`, `Mathlib.Topology.Homotopy.*`.
- Sheaf cohomology of complex manifolds: almost certainly not present yet.
- Riemann-Roch, Serre duality: expected absent at this level of generality.
- Quotient of a manifold by a discrete group action: per Rothgang, charted-space instance is in review — may or may not be present at the pinned commit. Check.

Output of Phase B lives in `docs/survey.md` (to be written).

## Phase C — Pick a construction

Three options from the Zulip discussion:

### Option 1: Period lattice `ℂ^g / Λ`

- `Λ` = image of `H₁(X, ℤ) → ℂ^g` via `γ ↦ (∫_γ ω_1, ..., ∫_γ ω_g)` for a basis `ω_i` of holomorphic 1-forms.
- **Pros**: most classical, matches undergraduate textbook presentations, gives the complex-torus structure for free.
- **Cons**: needs integration along loops on a general Riemann surface (not just ℂ). Also needs a basis of holomorphic 1-forms, which is essentially `H⁰(X, Ω¹_X)` — needs finite-dimensionality.

### Option 2: Pic⁰(X)

- `Pic⁰(X)` = degree-zero divisors modulo principal divisors.
- **Pros**: purely algebraic; avoids integration. Abel-Jacobi map is obvious (`P ↦ [P - P_0]`).
- **Cons**: getting the complex-manifold structure on it requires Riemann-Roch.

### Option 3: `H¹(X, 𝒪) / H¹(X, ℤ)`

- Sheaf-cohomological.
- **Pros**: cleanest theoretically, basis-free, modern.
- **Cons**: needs sheaf cohomology for complex manifolds in Mathlib (almost certainly absent).

### Claude's suggested variant (basis-free)

`Jacobian X := (H⁰(X, Ω¹_X))ᵛ / image of H₁(X, ℤ)` via the period pairing. A cleaner restatement of Option 1 that doesn't pick a basis.

### Decision criterion

Pick the option that minimizes the amount of missing-in-Mathlib machinery we have to build ourselves. Likely Option 1 in the basis-free form, but hold on the decision until Phase B is complete.

## Phase D — Build the API

Whichever construction we pick:

1. Define `Jacobian X` and give the topological / group / manifold instances.
2. Define `ofCurve` (Abel-Jacobi).
3. Prove `genus_eq_zero_iff_homeo` — needs that genus-0 compact Riemann surfaces are biholomorphic to `ℂP¹ ≃ S²`. May need uniformization.
4. Prove `ofCurve_inj` — Abel's theorem.
5. Define `pushforward`, `pullback`, `ContMDiff.degree`.
6. Prove functoriality.
7. Prove `pushforward_pullback = deg • id` — the payoff theorem.

## Phase E — Blueprint (at the end, not the start)

Once the Lean builds and the main theorems are proved (or the axiom/sorry inventory is clearly scoped), write a Leanblueprint / Verso-style blueprint retrospectively. Deferred per house convention.

## Open questions

- Does the pinned Mathlib commit have `modelWithCornersSelf` aliased to `𝓘(ℂ, E)`? (Rothgang mentioned the notation; Buzzard's file still uses `modelWithCornersSelf ℂ (Fin (genus X) → ℂ)` in some places and `𝓘(ℂ)` in others — possible internal inconsistency.)
- What is the cleanest Mathlib API for "discrete subgroup of a finite-dimensional complex vector space acting by translation"? This drives the period-lattice quotient.
