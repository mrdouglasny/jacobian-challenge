# UNWIND route — discharging `UnwindRegularity G D` for the concrete fine-sheaf `G` (2026-06-10)

> **STATUS 2026-06-11: LANDED (conditional).**  `unwindRegularity_concrete_of_isolated`
> (`SerreUnwindDetect.lean`, Part 5) proves `UnwindRegularity G D` for the concrete fine-sheaf
> `G`, sorry-free and standard-3, conditional on the cover-isolation discipline
> `BadPointsIsolated 𝔇 K D`.  The unconditional `∀ D` discharge is blocked exactly on the
> non-isolated-point evaluation — see `UNWIND_BLOCKER.md`.

Branch `feat/keystone-unwind` (on top of `feat/keystone-r6d2`: MLTie, MeroVanish, Descent,
DescentVanish all landed sorry-free).  Target: `SerreUnwind.lean:275`
`GlobalResidue.UnwindRegularity G D` for
`G := (cousinResidueData_of_witnessR …).toGlobalResidue` (res = `resCocycle` descended).

## The chosen route (cheapest honest path)

`UnwindRegularity G D` unfolds (contrapositive) to a **detection** statement:

> for every `E ≤ D` and `v ∈ L(K−E)` NOT in the image of `L(K−D)`, there is a test class
> `ξ ∈ H¹(𝒪_E)` with `h1InclMono ξ = 0` and `(G.pairing E v) ξ ≠ 0`.

(Given the factorization `pairing E v = lam ∘ incl`, evaluating at `ξ` gives
`pairing E v ξ = lam (incl ξ) = lam 0 = 0`, contradiction.)  This is the *minimal honest
statement*: no full Laurent-pairing coefficient formula, only "pairing nonzero against SOME
kernel class at each offending point".

### Order bookkeeping at the forced bad point

`v ∉ range(lSysInclMono)` ⟺ the representative `f ∉ linearSystem (K−D)` (germ-zero junk
does not move `orderW`), ⟺ ∃ `b` with `n := orderW f b` finite and
`E b − K b ≤ n < D b − K b` (lower bound from `f ∈ L(K−E)`).  In particular `E b < D b`:
**bad points are jump points of `E ≤ D`** — forced by `v`, not cover-chosen
(R6D2_BLOCKER §2 wall (a)).

### The test class — LocallyRealizable kills the E-membership wall (wall (b))

Set `k := K b ≥ 0`, `m := n + k` (so `E b ≤ m ≤ D b − 1`), `Ě := E + (m − E b)·b`
(so `Ě b = m`, `Ě = E` off `b`, `E ≤ Ě` and `Ě + b ≤ D`).  The port's **local
Mittag–Leffler witness** `FiniteCover.LocallyRealizable` (PROVEN for the chart-disk cover,
`SkyscraperProductWitness.locallyRealizable_chartDiskCover`) supplies a germ
`γ ∈ 𝒪_{Ě+b}(U j₀)` with top Laurent coefficient `1` at order `−(m+1)`
(`coeffGermLin`, exact order `−(m+1)` via `ker_coeffGermLin`).  Crucially `γ ∈ 𝒪_{Ě+b}`
already encodes **all the `E`-negative zero requirements** on `U j₀` — the interpolation
problem the R6D2 blocker §2 called "level bookkeeping at `E`" is solved by the realizability
witness, not by explicit Blaschke/Hermite factors.

The test cochain is `n̂ := Pi.single j₀ γ`, the test cocycle `η := δ⁰ n̂`:

* `η ∈ Z¹(𝒪_E)` — overlaps avoid `b` (isolation needed HERE, see the wall below), where
  `𝒪_{Ě+b} = 𝒪_E`;
* `h1InclMono [η] = 0` in `H¹(𝒪_D)` — `γ ∈ 𝒪_D(U j₀)` since `m + 1 ≤ D b`, so `η ∈ B¹(𝒪_D)`;
* `pairing E v [η] = res(cup v [η])` with `cup v η = δ⁰(globalGerm f · n̂)`
  (`cupCochain1_comp_cechDelta0`) — a one-bad-point **meromorphic coboundary** whose
  part-product with the slot has order EXACTLY `n + (−m−1) + k = −1` at `b`
  (order additivity, all three factor orders exact) — a **simple pole with residue
  `r = f_n·1·u(β) ≠ 0`** (minimal orders pair uniquely); at the K-points the product
  extends (DescentVanish product-germ trick) and the contribution dies.

### The evaluation engine (the new analytic content)

`MeroVanish.resFunctional_eq_zero_of_mero_coboundary` generalized from "all bad-point
slot-products extend ⟹ 0" to "one marked bad point has a simple-pole slot-product
(`SlotProductSimplePoleAt`, residue `r`), the rest extend ⟹ `resFunctional = −r`".
NO higher-order Cauchy–Pompeiu ladder: the Leibniz absorption (slot analytic ⟹ pull `g̃`
inside `∂̄`) reduces the surviving Stokes term at the marked chart to
`∫ ∂̄(pouCoeff·(r·(ζ−α)⁻¹)) + ∫ ∂̄(C∞c repaired remainder) = −π·r + 0` — the R0 atom
`integral_dbar_smearedSimplePole` plus the existing `pointRepair` Stokes kill.  Sign check
against MLTie: parts `h = −mlPart` give `resFunctional = −(−r·g(α)) = +r·g(α)` ✓.

## What remains open (the genuine wall)

The evaluation engine (like ALL of MLTie/MeroVanish) requires the bad point `b` to be
`MLIsolated` — in a single cover set — because the PoU weights must be locally constant
near the pole for the relocation/reinsertion kills.  The forced `b` need not be isolated in
the fixed cover, and since `E` ranges over ALL divisors `≤ D` inside `UnwindRegularity`,
no fixed-cover isolation discipline can cover every instance (bad points live in
`supp(D−E)`, which is arbitrary as `E` varies).  So the final theorem here is

> `UnwindRegularity G D` holds **given that every jump point of every `E ≤ D` involved is
> cover-isolated** — packaged per-instance; the unconditional `∀ D` discharge needs the
> **non-isolated-point evaluation**: the multi-chart PoU Cauchy–Pompeiu where the smeared
> pole splits across all charts containing `b` and only the SUM of chart contributions
> telescopes to the residue (`∑ρ ≡ 1` near `b`).  Cochain-side the multi-chart matching
> principal parts are ALREADY available (the skyscraper `coneB0` construction realizes
> compatible coefficient cochains on the whole star of `b`) — the wall is purely the
> integral evaluation.  See `UNWIND_BLOCKER.md`.

## File plan

1. `FineResidue/MeroVanish.lean` (in-place extension): `SlotProductSimplePoleAt`,
   `integral_dbar_pouCoeff_pouAverage_eq_residue` (marked chart),
   `resFunctional_eq_neg_residue_of_mero_coboundary` (engine headline).
2. `FineResidue/UnwindDetect.lean` (new): the abstract detector reduction
   `unwindRegularity_of_detects` (pure linear algebra, any `G`), bad-point extraction
   `exists_bad_point_of_notMem_range`, the isolated-point detector
   `exists_detecting_class_of_isolated` (the construction above), and the conditional
   headline `unwindRegularity_concrete_of_isolated`.
