# Path to `FiniteDimensional ℂ (HolomorphicOneForms X)` — Montel approach

## Decision

We pursue the **Montel / compactness** route to prove
`FiniteDimensional ℂ (HolomorphicOneForms X)` for X a compact connected
complex 1-manifold. This is the classical approach used in
Ahlfors–Sario and Rudin.

**Why not Cartan–Serre or Hodge?** Both require elliptic PDE theory on
manifolds, which Mathlib essentially lacks.

**Why not Riemann–Roch?** Would require GAGA (compact Riemann surface ≃
algebraic curve), also not in Mathlib.

**Why Montel?** Mathlib has:
- `MontelSpace` abstraction (bounded closed ⇒ compact).
- `FiniteDimensional.of_isCompact_closedBall₀` (Riesz).
- Maximum modulus on compact complex manifolds.
- `ContMDiffSection` with add/smul structure.

The bulk of the work — *Montel's theorem for holomorphic bundle
sections* — has a concrete proof via Cauchy estimates on charts +
Arzelà–Ascoli; no sheaf cohomology required.

## Outline

1. **Norm on `HolomorphicOneForms X`.** Define
   `‖α‖ := sup_{x ∈ X} ‖α x‖` (well-defined since X compact + α
   continuous as a bundle section).
2. **Banach structure.** `HOF X` with this norm is a normed ℂ-vector
   space; completeness (Banach) follows from uniform limits of
   holomorphic sections being holomorphic.
3. **Cauchy estimates in charts.** For a chart `φ : U → ℂ` and α
   written locally as `f dz` with `f` holomorphic on `φ(U)`, derivatives
   of `f` are bounded by `‖α‖ / dist(z, ∂φ(U))`.
4. **Equicontinuity.** Bounded sets in `HOF X` are equicontinuous (via
   Cauchy estimates + uniform control on a finite atlas).
5. **Arzelà–Ascoli.** Bounded + equicontinuous + compact base ⇒ closed
   unit ball is compact.
6. **Riesz.** Compact closed ball ⇒ finite-dimensional.

## Estimated schedule

Roughly 2–4 months of focused Lean work:

| Step | Weeks | Output |
|------|-------|--------|
| 1–2  | 2–3   | Norm + Banach structure on `ContMDiffSection` |
| 3    | 2–3   | Cauchy estimates on charts; bridge `ContMDiff 𝓘(ℂ) ω` ↔ `AnalyticOn ℂ` |
| 4    | 2–3   | Equicontinuity of bounded holomorphic sections |
| 5–6  | 2–3   | Arzelà–Ascoli for bundle sections + Riesz assembly |

## Why this is also a Mathlib PR

- Norm on `ContMDiffSection` for compact base — general-purpose.
- Montel for holomorphic bundle sections — classical missing lemma.
- Cauchy estimates on complex manifold charts — classical missing
  lemma.
- Riesz-adapted finite-dim conclusion for holomorphic sections —
  foundational.

Each of these pieces is independently useful and should be upstreamed
to Mathlib.

## Reference

Ahlfors, L. and Sario, L. *Riemann Surfaces*, Princeton, 1960 —
Ch. II §5 for Montel. Rudin, *Real and Complex Analysis*, Ch. 14 for
the planar case as a template.

## Current state (checkpoint)

`Jacobians/Montel.lean` compiles as a skeleton with concrete
foundations:

- `tangentOne x : TangentSpace 𝓘(ℂ, ℂ) x` — the model-space unit tangent
  vector (directly `1 : ℂ` via defeq).
- `HolomorphicOneForms.eval α : X → ℂ` — scalar evaluation of a
  cotangent section via `α.toFun x (tangentOne x)`.
- `HolomorphicOneForms.supNorm α : ℝ` — `sSup` of `‖eval α x‖` over X.
- `HolomorphicOneForms.eval_continuous` — SORRY; bundle-level
  continuity of the evaluation.

The `eval_continuous` sorry is the first concrete content-level step.
To close it we need either:
1. Apply `ContMDiff.clm_apply_of_inCoordinates` with an appropriate
   "constant tangent" section, OR
2. Use trivializations of the `Bundle.ContinuousLinearMap` Hom-bundle
   directly on a finite atlas and glue.

Approach (1) is blocked because `tangentOne` is NOT a globally smooth
vector field (it's "constant 1 in model space", which depends on chart
trivialization and isn't globally coherent under arbitrary chart
changes). Approach (2) is more hands-on but requires writing out the
coordinate change via chart derivatives.

## Session log (2026-04-21)

- Decision recorded (this doc + commit `5009a16`).
- Skeleton `Jacobians/Montel.lean` landed (commit `109419c`).
- `tangentOne` simplification + `eval`/`supNorm` definitions (commit
  `68e4157`).
- Partial unfolding toward `eval_continuous` — stuck at bundle-section
  evaluation machinery (commit `04377fe`).

## Refined findings (further exploration)

After deeper investigation, the `α.eval` approach has a fundamental
issue: `tangentOne x = 1 : ℂ` is NOT a globally continuous section of
the tangent bundle. The "constant 1 in model space" depends on chart
trivialization, and non-trivial chart transitions (chart derivatives ≠
identity) break the coherence.

Concretely: `ContMDiff.clm_bundle_apply` requires BOTH sections to be
smooth; `tangentOne` fails smoothness globally.

### Better approach: use a Riemannian metric

Mathlib has `Bundle.ContMDiffRiemannianMetric` (in
`Mathlib/Geometry/Manifold/VectorBundle/Riemannian.lean`). A smooth
Riemannian metric on the tangent bundle gives:
- Inner product on each fiber.
- Norm on tangent vectors.
- CLM operator norm on cotangent vectors (α(x) : T_x → ℂ).
- Pointwise `‖α(x)‖` — continuous as the CLM norm + smooth metric.
- Sup over compact X = finite norm.

**Blocker**: constructing a smooth Riemannian metric on X requires a
partition of unity argument. Mathlib has PoU in
`Mathlib/Geometry/Manifold/PartitionOfUnity.lean` but tying it to
Riemannian metric construction is non-trivial.

### Alternate: use existing `Bundle.ContinuousLinearMap` trivialization

Rather than constructing a canonical norm, define sup-norm via a
SPECIFIC finite atlas (compactness gives finiteness). For each chart,
α's trivialization gives a local holomorphic function; sup of
sup-norms of these local representatives is a legitimate norm.

This avoids the Riemannian metric construction but requires writing
out the trivialization extraction explicitly.

## Refined estimate

Step 1 (norm on HOF X) is **genuinely weeks of work** even with
Mathlib's Riemannian/trivialization infrastructure. The overall Montel
proof remains 2-4 months minimum.

## Current status (checkpoint 2)

- Skeleton + concrete `eval`/`supNorm` landed but `eval_continuous`
  has a structural issue (tangentOne non-smooth globally).
- Further progress requires switching approach to either:
  (a) Riemannian metric on TangentSpace via PoU, or
  (b) Chart-atlas based norm via `Bundle.ContinuousLinearMap`
      trivializations.
- Either path is substantial dedicated work (multi-week per sub-step).

## Current status (checkpoint 3 — Step 1 complete)

**Step 1 (norm on HOF X) is fully done.** `HolomorphicOneForms X` carries
a proper `NormedAddCommGroup` and `NormedSpace ℂ` structure (non-instance,
reducible defs — consumers opt in with `letI`).

The approach chosen: **chart-atlas (option b)**. Building blocks:

- `exists_finite_chart_cover` — finite chart cover of compact X.
- `chartCover` — canonical finite cover (via Classical.choose).
- `coverOpen` + shrinking lemma (`exists_iUnion_eq_closed_subset`) →
  `shrunkChart : X → Set X` giving compact refinement
  (`IsClosed + IsCompact (via CompactSpace)`).
- `localRep α x₀ y := α.toFun y ((trivializationAt ℂ TangentSpace x₀).symmL ℂ y 1)` —
  chart-local scalar representative of α.
- `continuousOn_symmL_const` (closed via `Trivialization.mk_symm` +
  `OpenPartialHomeomorph.continuousOn_symm`) and `localRep_continuousOn`.
- `chartNormK α x₀ := sSup ((‖localRep α x₀ ·‖) '' shrunkChart x₀)` —
  bounded chart-local sup-norm via continuity + compactness.
- `chartNormK_nonneg / chartNormK_zero / chartNormK_bddAbove`.
- `chartNormK_add_le` (triangle), `chartNormK_smul` (full homogeneity
  including c = 0 edge case handled separately).
- `supNormK α := chartCover.sup' chartCover_nonempty (chartNormK α ·)`.
- `supNormK_add_le` / `supNormK_smul` / `supNormK_neg` /
  `eq_zero_of_supNormK_eq_zero` (positive-definiteness).

Key insight for positive-definiteness: `T_y X ≃L[ℂ] ℂ` on the
trivialization base set (via `Trivialization.continuousLinearEquivAt`),
so `e.symmL ℂ y 1` is a spanning vector of `T_y X` (1-dim over ℂ).
Vanishing of `localRep α x₀` on the spanning vector implies
`α.toFun y = 0` as a CLM (via `ContinuousLinearMap.ext_ring`).

Final packaging: `AddGroupNorm.toNormedAddCommGroup` +
`NormedSpace.mk` via homogeneity.

## Next (Step 2+)

- Completeness (Banach): uniform limits of holomorphic sections are
  holomorphic. Requires Cauchy formula for limit interchange.
- Cauchy estimates on `localRep` (holomorphic functions in chart).
- Equicontinuity of bounded families.
- Arzelà–Ascoli for bundle sections.
- Riesz: compact closed ball ⇒ finite-dimensional.
