# Dolbeault comparison — chart-disk cover + forward operator (design plan)

Scope/design pass requested 2026-06-02 (after `dolbeault_to_cech` was decomposed into a sorry-free
`liftQ` + two named analytic kernels). Decision taken: **add a chart-disk cover structure** and build
the forward cocycle operator on it. This doc fixes the architecture before the build.

Companion: `docs/architecture_map.md` (DAG), `DolbeaultComparisonProof.lean` (the 5 remaining sorries),
`DbarDiskCohomology.lean` (the DONE disk-level PDE engine).

## What is already DONE (do not rebuild)

* `DbarDiskCohomology.dbar_solvable_ball` — `∂̄u = g` solvable on **all of** `ball c r` (sorry-free).
* `DbarDiskCohomology.differentiableAt_of_dbar_eq_zero` — `∂̄f = 0 ⟹ f` holomorphic (Wirtinger).
* `DbarDiskCohomology.dbar_holo_splitting_ball` — `H¹(disk,𝒪)=0` engine.
* Chart bridge `dbar_apply_one_eq_dbarDisk` (intrinsic `∂̄` read in a chart `= DbarDisk.dbar` of the
  pullback) + Wirtinger chain rule `dbarDisk_comp_holo` + global lift `exists_smoothLift_of_chartFun`.
* `OmegaD 0 U = {holomorphic}` (meromorphic + order ≥ 0); cocycle membership = holomorphy on overlaps.
* `cechDelta0_mem_ker_cechDelta1` — `cechDelta0 c` is a cocycle for ANY germ-class cochain.

## The architectural problem this solves

The comparison runs over a generic `FiniteCover` with an abstract `IsLeray` (each `U i` merely
*simply connected*). Solving `∂̄u_i = g` on a whole abstractly-simply-connected `U_i` would need
**uniformization (Riemann mapping)** — not in Mathlib, enormous. Restricting to a cover whose sets are
honest **coordinate disks** makes `dbar_solvable_ball` directly usable (pull `g` back through the
chart, solve on the ball, push forward).

## Proposed structure: `ChartDiskCover`

Bundle a `FiniteCover` (so all existing `𝔘.cechH1 / cocycles1 / coboundaries1` machinery applies
verbatim) with per-index coordinate-disk witnesses.

```
structure ChartDiskCover (X) [the manifold typeclasses] extends FiniteCover X where
  center : ι → X
  radius : ι → ℝ
  radius_pos : ∀ i, 0 < radius i
  -- the chart at (center i) carries U i onto the coordinate ball:
  source_eq : ∀ i, (chartAt ℂ (center i)).source = (U i : Set X)        -- U i IS a chart source
  ball_sub_target : ∀ i, Metric.ball (extChartAt 𝓘(ℂ) (center i) (center i)) (radius i)
                          ⊆ (extChartAt 𝓘(ℂ) (center i)).target
  image_eq_ball : ∀ i, (extChartAt 𝓘(ℂ) (center i)) '' (U i)
                          = Metric.ball (extChartAt 𝓘(ℂ) (center i) (center i)) (radius i)
```

Open design choices (decide at build time, pick the one that minimizes `extChartAt` source/target
bookkeeping):
* **(D1) `U i` = chart source vs. `U i` = chart⁻¹(ball).** If `U i` is exactly a chart *source*, the
  chart is a global homeomorphism `U i ≃ target`; but `target` need not be a ball. If `U i` =
  `chart⁻¹(ball) ∩ source`, then the chart-image is a ball but `U i` is a proper subset of the source.
  The second matches `dbar_solvable_ball` (image = ball) and is preferred; `image_eq_ball` above
  encodes it. Keep `source_eq` only if it simplifies; otherwise drop and carry the preimage form.
* **(D2) `extChartAt 𝓘(ℂ)` vs `𝓘(ℝ,ℂ)`.** They are defeq (`rfl`); use `𝓘(ℝ,ℂ)` to match the existing
  `∂̄`/`dbar` machinery in `DolbeaultComparisonProof`.

A `ChartDiskCover` extends `FiniteCover`, so `𝔘.toFiniteCover.cechH1 0` etc. are unchanged. The
forward operator is stated against `(𝔘 : ChartDiskCover X)`.

> **Existence of such a cover** (every compact ℂ-manifold has a finite chart-disk cover) is a
> *separate* lemma, not needed to define/use the operator. It IS needed eventually to instantiate the
> comparison; flag it as its own honest sorry `exists_chartDiskCover` rather than blocking on it.

## Forward operator pipeline (kernel 1: `dolbeaultToCechCocycle`)

For `g : ↥(OneFormsZeroOne X)` and index `i`:

1. **Pullback (cutoff-free).** Read `g` in the chart at `center i` as a planar smooth function
   `Gᵢ : ℂ → ℂ` on the ball — the Wirtinger datum `x ↦ g x (frame⁻¹)`, NO bump cutoff (the whole
   `U i` is the disk, so the point-local `exists_chartPullback_zeroOne_datum` cutoff is unwanted).
   Reuse `contMDiffAt_chartRead_datum` + `frameVector_eq_inv_deriv_transition` for the value, but
   take `Gᵢ` = the honest pullback `Φ ∘ e₀.symm` on the ball (drop the `χ` factor).
2. **Solve.** `dbar_solvable_ball Gᵢ (center-coord) (radius i)` ⟹ `fᵢ : ℂ → ℂ`, `∂̄fᵢ = Gᵢ` on the ball.
3. **Push forward + lift.** `uᵢ := fᵢ ∘ (chart at center i)` on `U i`; intrinsic `∂̄uᵢ = g` on `U i`
   via the chart bridge `dbar_apply_one_eq_dbarDisk` + the chain-rule `dbarDisk_comp_holo` (the same
   `conj(τ′)` cancellation already proven for the point-local case, now on the whole disk).
4. **Germ + cocycle.** `c := fun i => toGerm (U i) uᵢ : Cochain0`; output `cechDelta0 c`.
   - In `ker cechDelta1`: `cechDelta0_mem_ker_cechDelta1` (free).
   - In `sections1 0`: on overlap `U_i ∩ U_j`, `∂̄(u_j − u_i) = g − g = 0` ⟹ `u_j − u_i` holomorphic
     (`differentiableAt_of_dbar_eq_zero`) ⟹ germ ∈ `OmegaDGerm 0`.

## The linearity question (the one real fork in kernel 1)

`dolbeaultToCechCocycle` is typed `→ₗ[ℝ]` into `↥(cocycles1 0)` — i.e. it must be linear **at the
cochain level**, which forces the solution `g ↦ uᵢ` to be linear. Two routes:

* **Route A (recommended): expose a linear solve operator.** `dbar_solvable_ball` is an `∃`; under the
  hood `DbarDisk.dbar_solvable_of_compactSupport` is the Cauchy-transform convolution, which IS linear.
  Refactor `DbarDisk` to expose the solve as a genuine `ℝ`-linear map (`cauchyTransform : (ℂ→ℂ) →ₗ[ℝ]
  (ℂ→ℂ)` or a `→L`), with `dbar_solvable_ball` recovered as its property. Then steps 1–3 compose linear
  maps and the cochain-level operator is honestly linear. Pro: keeps the current sorry-free `liftQ`
  decomposition intact; the linear solve is reusable (round-trips, inverse map). Con: a localized
  `DbarDisk` refactor + the pullback (step 1) and lift (step 3) must also be exhibited as linear (they
  are — `g ↦ g x (frame⁻¹)` is `ℝ`-linear in `g`; precomposition with the chart is linear).
* **Route B: well-defined-mod-coboundary.** Drop the `cocycles1`-valued linear operator; define
  `dolbeault_to_cech` directly into `cechH1` via `Classical.choice` of solutions, proving `map_add` /
  `map_smul` at the quotient level (choices differ by holomorphic ⟹ coboundary ⟹ equal in `cechH1`).
  Pro: no `DbarDisk` refactor, uses the `∃` lemmas as-is. Con: discards the current decomposition;
  heavy coboundary-chasing for additivity/homogeneity; `dolbeaultToCechCocycle` / its `_dbarImage_le`
  would be replaced by a different (and arguably messier) interface.

**Recommendation: Route A.** It preserves the committed decomposition, yields a reusable linear solve,
and the extra linearity obligations (pullback, lift) are routine `ℝ`-linearity of evaluation +
precomposition.

## `dolbeaultToCechCocycle_dbarImage_le` (kernel 2)

Given Route A's operator: `g = ∂̄h` (`h : SmoothCFunctions X` global). Then `uᵢ − h|_{U i}` is
holomorphic on `U i` (`∂̄(uᵢ − h) = g − g = 0`), so `{toGerm (uᵢ − h)} ∈ sections0 0`, and
`cechDelta0 {uᵢ} = cechDelta0 {uᵢ − h}` (the global `h` telescopes to `0` under `cechDelta0`) ∈
`coboundaries1 0`. Hence in the kernel of the composite to `cechH1`. Mostly algebra once kernel 1's
operator and the "two solves differ by holomorphic" lemma exist.

## Recommended build sequence

1. `ChartDiskCover` structure (+ choose D1/D2) — small, no proofs.
2. Route-A linear solve operator in `DbarDisk` (expose Cauchy transform as linear; re-derive
   `dbar_solvable_ball` from it) — localized analytic refactor.
3. Cutoff-free linear chart-pullback `g ↦ Gᵢ` on the disk (refactor the `χ`-free core out of
   `exists_chartPullback_zeroOne_datum`).
4. `dolbeaultToCechCocycle` (compose 2+3 + push/lift + cocycle membership). Closes kernel 1.
5. `dolbeaultToCechCocycle_dbarImage_le`. Closes kernel 2 ⟹ `dolbeault_to_cech` fully grounded.
6. (separate track) `cech_to_dolbeault` — smooth-section gluing; then the two round-trips.
7. (instantiation, deferred) `exists_chartDiskCover`.

Estimated: steps 1–5 are the forward half; the genuine new work is step 2 (linearize the Cauchy
transform) + step 3 (cutoff-free pullback) + the disk-global versions of the already-proven point-local
chart-transport. No greenfield PDE — the disk solve and the Wirtinger machinery are done.
