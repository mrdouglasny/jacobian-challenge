# L2a — `Differentiable ℂ (liouvilleGlobalNumerator form)` — verified blueprint

*2026-06-07. The remaining hard core of Liouville L2. Architecture pinned and
Mathlib lemma names VERIFIED against the project's pin (Gemini-3.1-pro proposed
the route; the lemma names below were checked with `lake env lean`, correcting
Gemini's hallucinated `Complex.differentiableAt_of_continuousAt_of_…`). This is
L2a "branch-point regularity" — flagged in the plan as likely the hardest item.*

## The object
`liouvilleGlobalNumerator form : ℂ → ℂ` (`Axioms/HyperellipticLiouville.lean:216`)
is defined by `by_cases H.f.eval z = 0`:
- **branch** (`f z = 0`): value `= liouvilleProjYNumerator form (branchPoint z) _ (proj (inl branchPoint)) 0` — the projY (`w = y`) numerator at `w = 0`.
- **non-branch** (`f z ≠ 0`): `y := Classical.choose (IsAlgClosed.exists_eq_mul_self (f z))`, `a := (z,y)`, value `= liouvilleProjXNumerator form a hpY (proj (inl a)) z`.

The `Classical.choose` is **discontinuous** (can jump between the two sheets
`±y`) — this is the source of all the difficulty.

## Architecture (removable singularity)
`Differentiable ℂ G` ⟺ `∀ z₀, DifferentiableAt ℂ G z₀`. Split `by_cases f z₀ = 0`:

### Piece 1 — non-branch `AnalyticAt G z₀` (`f z₀ ≠ 0`).  REUSABLE.
Goal: `G =ᶠ[𝓝 z₀] liouvilleProjXNumerator form a₀ hpY₀ q₀` for the fixed `a₀`
built at `z₀`, then `Filter.EventuallyEq.analyticAt` + the existing
`liouvilleProjXNumerator_analyticAt` (LiouvilleSupport.lean:94, takes
`z ∈ target` + `hQ`). The chart target is open ∋ z₀ (`open_target.mem_nhds`).
**Subtlety:** the EventuallyEq is NOT a one-line overlap. For `z` near `z₀`
(`f z ≠ 0`) the def picks `a'(z) = (z, Classical.choose …)` on a possibly
*different sheet* than `a₀`'s analytic continuation. Two facts compose:
- same-sheet: `liouvilleProjXNumerator_eq_of_projX_overlap`
  (LiouvilleSupport.lean:255) — needs `hz : z ∈ (affineChartProjX a₀ hpY₀).target`
  AND `hSrc : (affineChartProjX a₀ hpY₀).symm z ∈ (affineChartProjX a'(z) hpY'(z)).source`.
- cross-sheet: the numerator `coeff_q · y` is invariant under `y ↦ -y, q ↦ ι q`
  (hyperelliptic anti-invariance `ι*ω = -ω`: both `coeff` and `y` flip sign).
  Source: `AntiInvariance.lean` / `EvenForm.lean` cocycle lemmas — find the
  exact `coeff (ι q) = - coeff q`-type statement and the sheet-swap on
  `liouvilleProjXNumerator`. **This cross-sheet step is the open sub-task of P1.**

### Piece 2 — isolated roots.  TRACTABLE (done, see LiouvilleSupport).
`∀ᶠ z in 𝓝[≠] z₀, H.f.eval z ≠ 0` — `H.f ≠ 0` (degree ≥ 2 even), root set finite,
eventually avoided on the punctured nhd. Mathlib: `Polynomial.finite_setOf_root` /
`Set.Finite.eventually_cofinite_nmem` through `𝓝[≠]`, or
`AnalyticAt.eventually_ne` on `f` after handling that `z₀` itself may be a root
(work on `f / (X - z₀)^mult` or just use finiteness of `(f.roots.toFinset \ {z₀})`).

### Piece 3 — branch `ContinuousAt G z₀` (`f z₀ = 0`).  HARD KERNEL (open).
The genuine removable-singularity content. Need
`Tendsto G (𝓝[≠] z₀) (𝓝 (G z₀))` where `G z₀ = projY-numerator at w=0`.
As `z → z₀`, `G z = coeff·y` with `y = √(f z) → 0` but `coeff ~ C/√f` blows up;
the finite limit is exactly the projY numerator (the form is regular in the
`w = y` coordinate). Requires a support lemma — Gemini's
`liouvilleProjX_tendsto_projY_branch`: the projX numerator pulled back along the
ramified coordinate `w ↦ z(w)` (`z = polynomialLocalHomeomorph.symm (w²)`,
2:1, even) tends to the projY numerator at `w = 0`. The even-in-`w` structure is
what makes the `z`-limit exist. **This whole lemma is open.**

### Piece 4 — assemble.  TRACTABLE once 1–3 land.
```
theorem liouvilleGlobalNumerator_differentiable (form) :
    Differentiable ℂ (liouvilleGlobalNumerator form) := fun z₀ => by
  by_cases hz₀ : H.f.eval z₀ = 0
  · -- removable singularity
    refine (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
      ?_ ?_).differentiableAt
    · -- hd : ∀ᶠ z in 𝓝[≠] z₀, DifferentiableAt ℂ G z   (Piece 2 ⇒ f z ≠ 0 ⇒ Piece 1)
      filter_upwards [piece2 z₀] with z hz using (piece1 form hz).differentiableAt
    · exact piece3 form hz₀          -- ContinuousAt
  · exact (piece1 form hz₀).differentiableAt   -- non-branch
```

## VERIFIED Mathlib lemma names (checked, current pin)
- `Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`
  `(hd : ∀ᶠ z in 𝓝[≠] c, DifferentiableAt ℂ f z) (hc : ContinuousAt f c) : AnalyticAt ℂ f c`
  — `Mathlib/Analysis/Complex/RemovableSingularity.lean:36`. **(Gemini's
  `Complex.differentiableAt_of_continuousAt_of_differentiableOn_compl_singleton`
  does NOT exist — do not use it.)**
- `AnalyticOn.analyticAt (hU : s ∈ 𝓝 z) : AnalyticOn 𝕜 f s → AnalyticAt 𝕜 f z`
  — `Analytic/Basic.lean:535` (already used at LiouvilleSupport.lean:99).
- `Filter.EventuallyEq.analyticAt : f =ᶠ[𝓝 x] g → AnalyticAt 𝕜 g x → AnalyticAt 𝕜 f x`.
- `AnalyticAt.differentiableAt`.

## Existing project building blocks (all sorry-free)
- `liouvilleProjXNumerator_analyticAt form a hpY q hQ {z} (hz : z ∈ target) : AnalyticAt ℂ (liouvilleProjXNumerator …) z`  (LiouvilleSupport.lean:94)
- `liouvilleProjXNumerator_eq_of_projX_overlap` (same-sheet)  (:255)
- `liouvilleBranchPoint_numerator_analyticOn` / `…_analyticAt_zero`  (:197 / :214)
- `form_coeff_eq_liouvilleProjXNumerator_div`  (:237)
- `liouvilleBranchPoint`, `liouvilleBranchPoint_mem_smoothLocusX`  (:24 / :30)

## Open sub-tasks (in order)
1. **P1 cross-sheet** — sheet-swap invariance of `liouvilleProjXNumerator`
   (anti-invariance), giving the non-branch `EventuallyEq`. Then P1 closes.
2. **P3** — `liouvilleProjX_tendsto_projY_branch` (ramified-pullback limit) ⇒
   branch `ContinuousAt`. The hardest.
3. **P4** — assemble `liouvilleGlobalNumerator_differentiable` (skeleton above).
Then L2 finishes with the already-built growth + `polynomial_decomposition_of_entire_growth`.
