# `deg_divisor_eq_zero` — the degree theorem (discharge plan)

**Statement.** On a compact connected Riemann surface `X`, a non-zero
meromorphic function has `#zeros = #poles` counted with multiplicity:
```
deg(div f) = ∑_p ord_p(f) = 0     (the degree of a principal divisor is zero).
```
Lean form (group layer, where `divisor` lives):
```lean
theorem deg_divisor_eq_zero (f : MeromorphicFunctionField X) :
    Divisor.deg X (MeromorphicFunctionField.divisor f) = 0
```

**Status.** Not an axiom and not a `sorry` — it is an **absent** classical fact,
referenced in prose by `SerreDualityAPI.lean:29` and `AbelTheorem.lean` as "the
residue theorem `deg(div f) = 0`." Introducing + proving it is the goal.

**Leverage (why this is the high-value next target).** It gates the negative-degree
vanishing `deg D < 0 ⇒ L(D) = 0`, which in turn unblocks:
- **`h1_eq_zero_of_deg_gt`** (Serre vanishing, `SerreDualityAPI.lean:92`): via
  `h¹(D) = h⁰(K−D)` (proved) + `deg(K−D) < 0` (using `canonicalDivisor_deg`, now
  proved) ⇒ `h⁰(K−D) = 0`.
- **`h0_of_deg_gt`** (`RiemannRochAPI.lean`): the proved `riemannRoch` identity +
  the same vanishing.
- The **adelic Serre-duality** crux (#103/#105) is the same `∑res = 0`.
- **`AX_AbelTheorem`**: principal divisors are degree 0 (its degree-0 restriction
  was added for exactly this reason).

**Route / effort.** ~**9–14 focused-days** (Codex). The hard *analytic* core (the
local-mapping theorem + local fiber-sum conservation) is **already vendored
sorry-free** (Wallace); the cost is the assembly + a layer bridge. **Vetted:**
Gemini deep-think (math, picked the slicker route) + Codex (Lean feasibility).

---

## What we already have (sorry-free, vendored Wallace)

The `Jacobians/Vendor/Wallace/HolomorphicForms/` modules give the analytic core:
- `analytic_local_mapping_theorem` (`AnalyticLocalMapping.lean:212`) — local normal
  form `z ↦ zᵏ`.
- `local_kfold_ramified_of_contMDiff` (`HolomorphicMap.lean:1082`) — a point of
  order `k` has exactly `k` simple preimages of every nearby value.
- `weightedFiberConservation_of_contMDiff` (`HolomorphicMap.lean:1199`) — the
  weighted fiber sum `∑_{x∈f⁻¹(y)} mult_x(f)` is **locally constant** in `y`
  (`∀ᶠ y in 𝓝 y₀`). **Caveat: it requires a compact *source*.**
- `mapAnalyticOrderAt` (`HolomorphicMap.lean:175`) = `ord_x(f − f(x))` — local
  multiplicity = vanishing order.
- `isHolomorphic_finite_fiber` (`HolomorphicMap.lean:648`) — fibers finite on
  compact `X`.

What is **missing** for `deg(div f) = 0`: (a) a global fiber-sum constancy usable
for a meromorphic `f` (the Wallace lemma needs a compact source — a meromorphic
function on `X` is not compact-source once poles are removed, *or* needs ℙ¹ as
target); (b) the pole/∞ sign bookkeeping; (c) the **layer bridge** (below).

---

## Two routes (both vetted feasible)

### Route A — the "Two-Halves" trick (Gemini; **avoids ℙ¹** — recommended for the analytic core)

Do **not** build ℙ¹ as a manifold. Compare `f` and `1/f` as proper maps to `ℂ`:

1. **Constant case:** `f = c ≠ 0 ⇒ div f = 0` (handle early; non-constant ⇒ fibers
   discrete/finite).
2. `f` restricts to a holomorphic `f₀ : X∖(poles) → ℂ`; `g₀ = 1/f : X∖(zeros) → ℂ`.
3. **Properness** (`X` compact): `f₀⁻¹(K)` is closed in `X` (a sequence
   approaching a pole has `|f₀| → ∞`, escaping bounded `K`), hence compact. Mathlib:
   `IsProperMap`, `Continuous.isProperMap`, `IsProperMap.isCompact_preimage`,
   `IsProperMap.isClosedMap` (`Topology/Maps/Proper/Basic.lean`).
4. **Global fiber-sum constancy** via a *compact-neighborhood trapping* argument
   (port Wallace's compact-source proof to proper maps, ~1 day): cover the finite
   fiber `f₀⁻¹(y₀)` by disjoint local-mapping nbhds `Uᵢ`; on a compact disk `K`
   around `y₀`, `f₀⁻¹(K)∖⋃Uᵢ` is compact, its image is closed and misses `y₀`,
   giving a nbhd `V` where every fiber is trapped in `⋃Uᵢ`, so the global fiber sum
   equals the sum of local ones ⇒ locally constant ⇒ constant `d`.
5. **Match.** `N_f(0) = #zeros`, `N_g(0) = #poles`. At a regular value `y ≠ 0`:
   `f₀(x) = y ⟺ g₀(x) = 1/y`, and `mult_x(g₀) = ord_x(1/f − 1/y) = ord_x(f − y) =
   mult_x(f₀)` (since `1/f − 1/y = (−(yf)⁻¹)(f − y)` and `yf` is a local unit when
   `f(x)=y≠0`). So `d = d'`, `#zeros = #poles`, `∑ord = 0`.

**Pros:** zero new geometry; only point-set topology + the vendored local core;
the ∞-bookkeeping collapses into evaluating `1/f` at `0`. **Cons:** the proper-map
fiber-constancy is a fresh ~1-day port; needs the layer bridge.

### Route B — complete the existing `MeromorphicToP1.lean`

The repo **already** has a partial ℙ¹ route: `toP1`, `toP1_contMDiff`,
`toP1_eq_infty_iff`, and the **pole** weighted-fiber sum
(`MeromorphicToP1.lean:541/549/555/584`). Missing: the matching **finite-value /
zero** weighted sum, and the **global constancy** upgrade (local → global on
connected ℙ¹ via `IsLocallyConstant` / `weightedFiberConservation`).

**Pros:** half-built; aligns with the existing ℙ¹ infrastructure; once global
constancy + the zero-sum land, `deg(div f)=0` is `fiberSum(0) = fiberSum(∞)`
directly. **Cons:** carries the ℙ¹ chart-at-∞ bookkeeping Gemini flagged as a
distraction; the global-constancy step still needs building.

---

## Shared infrastructure (needed by **both** routes — and the real cost)

Codex's verdict: the bottleneck is **not** the fiber-constancy (~1 day either way)
but the **layer bridge** and the wiring.

1. **The layer bridge.** `divisor` / `Divisor.deg` / `PrincipalDivisors` live on
   `MeromorphicFunctionField X` (a `CommGroup` quotient of nonzero reps); but `L(D)`
   / `riemannRochSpace` live on `MeroField X = MeroFunctions ⧸ GermZero` (a
   `Submodule`). **There is no connection.** Least-painful bridge (Codex): for a
   *nonzero* `F : MeroField X`, pick a representative and map to
   `MeromorphicFunctionField X` (using `orderAt_ne_top_of_exists`,
   `VanishingOrder.lean:558`), prove `orderAtMF p (toMF F) = orderAtField p F`,
   then reuse the existing `divisor`. **Do not** port a total `divisor` to
   `MeroField` (the `0` germ has order `⊤`, no honest divisor).
2. **`Effective D → 0 ≤ Divisor.deg X D`** — small finite-support lemma (currently
   absent; `Effective` at `RiemannRochSpace.lean:40`, `Divisor.deg` at
   `Divisor.lean:41`).
3. **`deg D < 0 ⇒ riemannRochSpace D = ⊥`** (hence `h0 D = 0`): a nonzero `F ∈ L(D)`
   gives `0 ≤ deg(divisorOf F + D) = deg(divisorOf F) + deg D = 0 + deg D = deg D`,
   contradicting `deg D < 0`. Uses `riemannRochSpace_orderBound`
   (`RiemannRochFinite.lean:215`) to get `Effective(divisorOf F + D)`.
4. **Wire Serre vanishing:** `h1_eq_zero_of_deg_gt` via `h1_eq_h0_canonical_sub`
   (proved) + `canonicalDivisor_deg` (proved) ⇒ `deg(K−D) < 0` ⇒ step 3. The same
   closes `h0_of_deg_gt`.

The valuation arithmetic for step 5 of Route A is well-supported (Mathlib
`Analysis/Meromorphic/Order.lean`: `meromorphicOrderAt_congr/_mul_of_ne_zero/_inv`).

---

## Vetting

### Gemini deep-think (2026-06-08) — math + route: **use the Two-Halves trick**

> "Your local-mapping core is exactly what you need. Pivot slightly away from
> building ℙ¹ and use the Two-Halves (`f` and `1/f`) proper-map route. It requires
> exactly zero new geometric definitions."

- Branched-cover idea is the standard, formalization-friendly path (avoids form
  integration / intersection theory). Two-Halves makes it slicker: no ℙ¹ manifold,
  no chart-at-∞ transition maps — the pole sign becomes trivial valuation arithmetic.
- **Gotchas:** handle `f = const` first (fibers not discrete otherwise);
  **properness** is the real topological ingredient (else fibers leak to infinity).
- The local→global step is easy *given properness*, via the compact-nbhd trapping
  argument (a ~10-line Mathlib point-set proof), not a heavy general theorem.

### Codex (GPT-5.4, 2026-06-08) — Lean feasibility: **Two-Halves preferable; ~9–14 days; cost = the bridge**

- Wallace API applies to `f₀ : (open ⊆ X) → ℂ` (`ℂ` is already `ChartedSpace ℂ`);
  but `weightedFiberConservation_of_contMDiff` needs a **compact source** — its
  internal trapping argument must be ported to proper maps (~1 day).
- All Mathlib ingredients present (`IsProperMap`, `IsCompact.image`,
  closed-in-compact, the `meromorphicOrderAt` lemmas). **No** general
  argument-principle / proper-holomorphic-degree theorem in Mathlib to reuse.
- **Found existing `MeromorphicToP1.lean`** (`toP1` + pole fiber-sum) — Route B is
  half-built; the missing finite-value sum + global constancy still need work.
- **Riskiest / real cost:** the `MeroField ↔ MeromorphicFunctionField` bridge and
  `deg D<0 ⇒ L(D)=0`, **not** the fiber-constancy. Estimate: analytic theorem
  **5–8 days**, bridge + vanishing **4–6 days**, total **9–14 days**.
- Verdict: Two-Halves is the right call vs. building new ℙ¹ machinery in this repo.

---

## Build order

1. **Shared, do first (independent of the analytic theorem):**
   - `Effective D → 0 ≤ Divisor.deg X D` (small).
   - The `MeroField`(nonzero) → `MeromorphicFunctionField` bridge +
     `orderAtMF = orderAtField`; a `divisorOf : {F : MeroField // F ≠ 0} → Divisor X`.
   - `deg D < 0 ⇒ L(D) = ⊥` **assuming** `deg_divisor_eq_zero` (so Serre vanishing
     can be wired before the analytic theorem lands).
   - Wire `h1_eq_zero_of_deg_gt` + `h0_of_deg_gt` from the above + `canonicalDivisor_deg`.
2. **The analytic theorem** (`deg_divisor_eq_zero`) via **Route A**:
   - constant case; `f₀`/`g₀` as holomorphic proper maps to `ℂ`;
   - port `weightedFiberConservation` to proper maps (global constancy);
   - the valuation match at a regular value ⇒ `#zeros = #poles`.
   - Fallback / cross-check: **Route B** (finish `MeromorphicToP1.lean`'s zero sum +
     global constancy) if the proper-map port proves harder than the ℙ¹ one.
3. Replace the prose "residue theorem" references with the proved theorem; close the
   Serre-vanishing + `h0_of_deg_gt` anchor `sorry`s (anchor sorrys 4 → 2).

## Recommendation

**Route A (Two-Halves)** for the analytic theorem — it is the cleaner, ℙ¹-free
path Gemini and Codex both endorse, reusing the vendored local-mapping core. Keep
**Route B** (the existing `toP1`) as a cross-check/fallback since it is half-built.
Do the **shared bridge + `deg<0 ⇒ L=0` first** (it is the real cost and it lets
Serre vanishing be wired immediately, modulo the one analytic theorem). This
discharges 2 more anchor `sorry`s and supplies the residue crux that adelic Serre
duality and Abel also need.

## References

- Forster, *Lectures on Riemann Surfaces* (GTM 81), §16 (the meromorphic-function
  degree); Miranda, *Algebraic Curves and Riemann Surfaces*, Ch. II/VI.
- Project: `Vendor/Wallace/HolomorphicForms/{HolomorphicMap,BranchedCover,AnalyticLocalMapping}.lean`
  (local core); `RiemannSurface/MeromorphicToP1.lean` (partial Route B);
  `RiemannSurface/MeromorphicFunctionField.lean` (`divisor`/`divHom`);
  `RiemannSurface/Cohomology/{RiemannRochSpace,RiemannRochFinite,SerreDualityAPI}.lean`.
