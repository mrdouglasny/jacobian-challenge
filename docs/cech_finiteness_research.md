# `finiteDimensional_cechH1` (G3b, Forster 14.9) — research + build plan

Research for the **next ladder node** after the `h0Dim_eq_lDim` bridge: proving
`FiniteDimensional ℂ (𝔘.cechH1 D)` (Forster *Lectures on Riemann Surfaces* Thm 14.9). Done while
the gluing/surjectivity agent finishes the bridge leaf. Companion to `docs/archive/dolbeault_ladder_derisk.md`
(which flagged this node as the biggest unmeasured risk: the germ-class vs sup-norm representation clash).

## Headline verdict — TEMPLATED, not greenfield

The de-risk feared finiteness was a ~800–1500 LoC greenfield analytic build. **It is largely a
*reuse* of the repo's existing Ω(X) Montel finiteness** (`Jacobians/Montel*`, ~95% done), which proves
the *same shape* of theorem (`FiniteDimensional ℂ (HolomorphicOneForms X)`) by the *same method*
(Montel ⟹ compact ⟹ Riesz). The "germ-vs-sup-norm clash" is resolved the way the repo already
resolved it for Ω(X): put a sup-norm on the analytic object, embed into bounded-continuous-functions
on an inner shrinking, Arzelà–Ascoli compactness, Riesz finite-dimensionality.

## What the repo ALREADY has (big reuse)

- **The nested triple cover** = Forster's `𝔘 ⋐ 𝔙` shrinking, *already built* (`Montel/Cover.lean`):
  `coverOpen x ⊇ chartOpen x ⊇ innerChartOpen x` with closures nested
  `innerShrunkChart ⊆ chartOpen ⊆ shrunkChart ⊆ coverOpen`. This is the "wiggle room" that makes the
  restriction map compact (bounded on the outer disk ⟹ relatively compact on the strictly-inner one).
- **Disk-level Montel** (`Montel/Compactness.lean`, ~1000 LoC, all proven):
  `uniformEquicontinuousOn_of_bounded_analyticOn`, `equicontinuous_localRep_inner_family`,
  `isCompact_univ_pi_closure_image_inner_bcf` (Arzelà–Ascoli on the bcf embedding),
  `analyticOn_of_pullback_tendsto_locally_uniformly` (locally-uniform limit of holomorphic is
  holomorphic), `exists_cauchy_deriv_bound` (Cauchy estimates). These are about holomorphic functions
  on chart disks — **directly the objects a `𝒪_D`-cochain restriction is built from.**
- **The sup-norm + bcf + Riesz pattern** (`Montel.lean`, `HolomorphicForms.lean`):
  `supNormK`/`supNormKAsAddGroupNorm` → `NormedAddCommGroup`, `embedInnerBcf : HOF →L bcf`,
  `closedBall_isCompact`, and the finish `FiniteDimensional.of_isCompact_closedBall₀ ℂ zero_lt_one`.
  This is exactly the Riesz "compact unit ball ⟹ finite-dim" endgame.
- **∂̄ on a disk** (`DbarDisk.lean`, G1, axiom-clean) — needed for the Leray vanishing
  `H¹(disk, 𝒪) = 0` (a chart-disk cover is then Leray, so `H¹(𝔘) = H¹(X)`).

## Mathlib inventory (verified at pin `8e3c989`, this session)

| Capability | Status | Name / note |
|---|---|---|
| `IsCompactOperator` + full API (comp, closed ideal, limits, closed-ball char) | **PRESENT** | `Analysis/Normed/Operator/Compact.lean` |
| Riesz lemma | **PRESENT** | `riesz_lemma`, `riesz_lemma_of_norm_lt` (`…/RieszLemma.lean`) |
| Fredholm alternative (spectral form) | **PRESENT** | `hasEigenvalue_or_mem_resolventSet`, `antilipschitz_of_not_hasEigenvalue` (`…/FredholmAlternative.lean`) |
| Arzelà–Ascoli | **PRESENT** | `Topology/UniformSpace/Ascoli.lean` |
| Riesz finite-dim from compact unit ball | **PRESENT** | `FiniteDimensional.of_isCompact_closedBall₀` (repo already uses it) |
| **"surjective + compact perturbation ⟹ finite codim" (Schwartz/Forster 14.8)** | **ABSENT** | the one genuinely-missing functional-analysis lemma |
| Banach space of holomorphic functions (sup-norm) | **ABSENT in Mathlib / PRESENT in repo** | repo's `supNormK`/bcf pattern fills it |
| coherent-sheaf / Cartan–Serre finiteness | **ABSENT** | (expected) |

## The two genuinely-new pieces (the residual risk)

1. **Schwartz's finiteness lemma** (Forster 14.8): for Fréchet/Banach `E, F`, `u : E → F` surjective
   continuous and `v : E → F` compact, `(u − v)(E)` has finite codimension in `F`. Mathlib has the
   ingredients (Riesz, compact-operator API, antilipschitz-from-Fredholm) but **not** the packaged
   statement. ~100–300 LoC. **Why it (rather than the cleaner Riesz route) is needed:** the naive Riesz
   route ("unit ball of `H¹` compact ⟹ finite-dim") presumes `H¹` is *Hausdorff*, i.e. `B¹ = im δ⁰` is
   *closed* — but closedness of `B¹` is itself a consequence of finiteness (circular). Forster's
   Schwartz lemma gives finite codim of the *image* directly, sidestepping a-priori closedness. So the
   robust route is the Schwartz lemma, not bare Riesz.
2. **The Leray / two-cover setup**: restriction `Z¹(𝔙) → Z¹(𝔘)` (𝔘 a shrinking of 𝔙) is **compact**
   (disk-Montel, reuse) and induces a surjection on `H¹` (chart-disks are Leray via the G1 ∂̄-disk
   vanishing). Feed `(restriction, δ⁰)` into the Schwartz lemma ⟹ `H¹(𝔘)` finite-dim. The Leray
   refinement bookkeeping (Čech, `H¹(disk)=0`) is real work but G1 is done.

## Representation fork (the clash, resolved)

- The **germ-class rep** (current `cechH1`, `Filter.Germ` over codiscrete) is the *right* rep for
  `h⁰` (junk-free, a plain finrank), the `h0Dim_eq_lDim` bridge, and the χ-additivity bookkeeping.
- The **sup-norm honest-function rep** (holomorphic functions on shrunk disk-intersections, `supNormK`)
  is the *right* rep for the finiteness/Montel argument.
- **Recommendation:** do NOT re-found on one rep. Run finiteness in the sup-norm rep, then prove a
  **comparison** `𝔘.cechH1 D (germ) ≃ₗ cechH1 D (sup-norm/honest)` (equal finrank suffices). The
  comparison is bounded: germ-classes and honest sections differ only by codiscrete junk, which does
  not change `H¹` (the same codiscrete↔𝓝[≠] bridge already proven in `CechH0`). This comparison is the
  price of the dual rep; it is *much* cheaper than re-deriving `h⁰`/χ in a topological rep.

## Recommended build sub-order

0. (G2 ∂̄-globalization is **not** needed here — finiteness uses only G1 ∂̄-*disk*. Defer G2 to the
   Serre node.)
1. `𝒪_D`-cochain sup-norm rep on the nested cover (reuse `supNormK`/bcf pattern). Sections of `𝒪_D`
   on a disk are meromorphic with `D`-bounded poles; clear the pole by the local factor, or reduce to
   `D = 0` first (the skyscraper twist handles general `D` downstream). **Start with `D = 0`.**
2. Compact restriction `C^q(𝔙) → C^q(𝔘)` (reuse disk-Montel `isCompact_…_inner_bcf`). *Likely easier
   than the repo's open Ω(X) sorry `exists_convergent_subseq_of_bounded` — cochains are plain functions
   on overlaps, with no cotangent-bundle reconstruction.*
3. Schwartz finiteness lemma (new, from Mathlib Riesz/compact API).
4. Leray surjection on `H¹` (G1 ∂̄-disk) + feed Schwartz ⟹ `H¹(𝔘, 𝒪)` finite-dim.
5. Comparison germ-rep ↔ sup-norm-rep ⟹ `FiniteDimensional ℂ (𝔘.cechH1 0)`; then general `D`.

## Net for the plan

Finiteness is **medium-large but de-risked**: dominated by reuse of the repo's HOF Montel + the
already-built nested cover + disk-Montel + G1. The dominant *new* risks are (i) the Schwartz
finite-codim lemma (bounded functional analysis) and (ii) the Leray/closed-range bookkeeping. The
representation clash is real but resolved by a cheap comparison iso, not a re-foundation. This
confirms the de-risk's `~800–1500 LoC, Med` estimate and lowers its variance. See
`docs/archive/dolbeault_ladder_derisk.md`, `docs/archive/riemann_roch_proof_plan.md §2`.

---

## ▶ DECOMPOSITION of the single remaining sorry `exists_cechModel` (2026-06-03)

State: the **entire abstract/FA spine is proven axiom-clean** (`Schwartz 14.8`, `rhoRaw_compact`,
`finiteDimensional_supH1`, `leray_surjective`). `finiteDimensional_cechH1_wired` is a sorry-free
consumer. The ONLY sorry is `exists_cechModel 𝔘 D : ∃ d c, Nonempty (𝔘.cechH1 D ≃ₗ[ℂ] c.supH1)`
(`CechFinitenessWiring.lean:282`). It is **monolithic** — these sub-obligations are entangled because
`c` and the equiv must be the model *built from* `(𝔘,D)`:

| # | Sub-obligation | Tractability | Reuse |
|---|---|---|---|
| G | `DiskOverlapData` geometry (`Uov` open, `Kov` convex compact ⋐ `Uov`) | **FREE** — round balls (`Metric.closedBall` convex compact); NOT the blocker | — |
| C1 | `Coboundaries.{C0,C2,C2cov,δ0,δ1,δ1cov}` δ-complex on BddHol cochains of the cover, `hδδ`, `hcomm` | medium (Čech δ algebra on `BddHol`) | `CechComplex` δ pattern |
| C2 | `Coboundaries.leray` field (every shrinking 1-cocycle = `δ⁰η + ρ·(cover cocycle)`) | **HARD** = disk-acyclicity `H¹(disk,𝒪)=0` assembled into the Čech leray field | `DbarDiskCohomology.dbar_solvable_ball` (PROVEN), `dbar_holo_splitting_ball` |
| K | The comparison `𝔘.cechH1 D ≃ₗ[ℂ] supH1` | **HARDEST** = germ↔BddHol bridge ∘ **Leray refinement-invariance** of `H¹` | CechH0 codiscrete↔`𝓝[≠]` bridge; Mathlib has NO Leray thm |

**The true wall is C2 (leray) + K (comparison incl. refinement).** K splits:
- **K-bridge**: germ-class `𝒪_D` cochains ↔ `BddHol` cochains on chart-images. The function-level
  analogue of `Montel.localRep_analyticOn_chartTarget` (chart-pullback of a holomorphic *function* is
  analytic) + boundedness on the relatively-compact shrinking + the CechH0 codiscrete↔`𝓝[≠]` junk
  identification. Templated, ~medium.
- **K-refine**: `𝔘.cechH1 D ≃ cechH1(chart-disk cover) D` — Leray cover-refinement invariance. Mathlib
  lacks Leray; this is a genuine Čech-cohomology theorem (refinement maps + acyclic-cover independence).
  The single biggest greenfield piece. If `𝔘` is ALREADY a chart-disk Leray cover, K-refine is trivial
  — so a first milestone is `exists_cechModel` **for chart-disk covers only**, deferring K-refine.

**Recommended executable order (first session of the wall):** (1) K-bridge atom — chart-pullback of a
holomorphic function is analytic (build/verify; likely partially in `CechH0`/`DolbeaultComparison`),
then the bounded restriction to `BddHol`. (2) C1 δ-complex. (3) C2 leray from the proven disk atoms.
(4) Assemble `exists_cechModel` for chart-disk covers (K-refine = id). (5) K-refine (Leray invariance)
last — the foundation piece. Each lands as a named lemma; the monolithic sorry shrinks as they close.
**Caveat (measured this session): no sub-piece lands sorry-free fully in isolation from `(𝔘,D)`** — the
equiv ties them — so progress is "shrink the sorry by building K-bridge/C1/C2 as standalone lemmas the
final assembly consumes," not "close a vacuous geometric lemma."

### ✅ K-BRIDGE PRIMITIVE LAYER COMPLETE (2026-06-03, all axiom-clean)

The reusable germ↔`BddHol` primitives are built (`CechModelBridge.lean` = pure ℂ; `CechModelManifold.lean`
= manifold side):
- `BddHol.ofAnalyticOn` — analytic+bounded on `U` ⟹ `BddHol U` (extend-by-zero normal form).
- `bddOn_of_analyticOn_subset_compact` — analytic on `U` ⟹ bounded on any compact `K ⊆ U`.
- `BddHol.ofAnalyticOnOfRelCompact` — `g` analytic on `U`, `U' ⋐ U` ⟹ `BddHol U'` (boundedness free).
- (manifold) `transition_analyticAt_of_mem`, `analyticAt_chart_change_to` — chart transition / own-chart→
  cover-chart analyticity at a GENERAL point (the existing `CechH0` versions are centre-only).
- (manifold) `analyticOn_pullback_of_holo` — chart-pullback of a holo section is `AnalyticOn` chart-image.
- (manifold) **`holoSectionToBddHol`** — the single-section bridge: holo `𝒪₀` section on `V ⊆
  (chartAt y).source`, restricted to `U' ⋐ (chartAt y)''V`, is a `BddHol U'` element (value = chart
  pullback). The per-overlap building block of the germ→`BddHol` cochain map.
⚠ INFRA LESSON: `variable` must list `[ChartedSpace]` BEFORE `[IsManifold]` — the reverse triggers
pathological instance resolution (400s timeout → 77s).

### ⛔ THE NEXT BLOCKER — convexity of overlaps (a real design fork)

The `DiskOverlapData.Kov` (per-overlap shrinking) must be **`Convex ℝ`** — the Montel restriction-
compactness `BddHol.isCompactOperator_restrictCLM` requires it (it threads `hKconv` into
`CechFiniteness.isCompact_closure_restrict_bddHolo`). But the chart-image of an overlap of *different*
charts is NOT convex (the transition map `φ_i∘φ_j⁻¹` distorts disks). So a `DiskOverlapData` built from a
generic cover cannot satisfy `hKconv`. Two resolutions:
- **(A, recommended) Generalize restriction-compactness to non-convex compact `K`** — sorry-free, via a
  finite cover of `K` by convex closed disks `Dᵢ ⊆ U` (compactness): `BddHol U → Π_i (Dᵢ →ᵇ ℂ)` is
  compact (`isCompactOperator_pi` + the convex atom per `Dᵢ`); `(K →ᵇ ℂ)` embeds isometrically (closed)
  into the product via `K ⊆ ∪Dᵢ`, and compactness reflects through a closed isometric embedding. ~80–150
  LoC functional analysis (no convexity of `K` needed for the underlying Arzelà–Ascoli — equicontinuity
  of bounded-holomorphic on compact `K ⊆ U` is from Cauchy estimates on small disks around each point).
  Then drop `hKconv` from `DiskOverlapData` (a shared-struct edit) — `Kov` = chart-image of the shrunk
  overlap (compact). **This is the concrete next executable lemma.**
- **(B) Build a convex/good cover** — a geodesically-convex cover (needs a Riemannian metric / exp map);
  heavier, brings in differential geometry the repo doesn't have.
After this: `DiskOverlapData` construction from `Montel.chartCover`/`ChartDiskCover` + the cochain map
(`Π_p holoSectionToBddHol`) + δ-commuting + the `leray` field (disk atoms) + the `cechH1≃supH1` comparison.

#### Non-convex restriction-compactness — executable sub-plan (Step 1 ✅ done)

Goal: `isCompactOperator_restrictCLM` for `K` compact (NOT convex) `⊆ U` open. **✅ DONE 2026-06-03**
(`BddHol.isCompactOperator_restrictCLM_of_compact`, commit `9d827e6`, axiom-clean — verified).
- **Step 1 ✅** `exists_finite_closedBall_cover` (`a400d8e`): finite convex-disk cover. (Ended up UNUSED
  by the route that landed; kept as a reusable utility.)
- **Step 2 ✅ — ROUTE B (Arzelà–Ascoli) landed, cleaner than the planned route a.** Instead of the
  embedding/gluing, uniform equicontinuity on non-convex `K` comes from a **single uniform Cauchy
  derivative bound on a thickened compact**: take `δ` with `cthickening δ K ⊆ U`, set `K' :=
  cthickening (δ/2) K` (compact `⊆ U`); `Montel.exists_cauchy_deriv_bound` (no convexity) gives
  `‖(f i)' ‖ ≤ L·C` on `K'`; for `x,y ∈ K` with `dist x y < δ/2` the convex ball `closedBall x (δ/2)
  ⊆ K'` contains both, so the 1-D mean-value inequality gives a single equicontinuity modulus on all of
  `K`. New lemmas (axiom-clean): `uniformEquicontinuousOn_of_bounded_analyticOn_of_compact` (the genuine
  new content), `isCompact_closure_restrict_bddHolo_of_compact` (convexity-free Montel atom),
  `isCompactOperator_restrictCLM_of_compact` (drop-in for the convex sibling minus `hKconv`; keeps
  `[CompactSpace K]`, already in scope at the `DiskOverlapData.Kov` call site). **Still TODO: drop
  `hKconv` from `DiskOverlapData` (shared-struct edit) so `Kov` = chart-image of the shrunk overlap.**

**✅ DiskOverlapData GEOMETRY DONE (2026-06-03, commit 7bd9d23, `CechModelGeometry.lean`, axiom-clean).**
`chartCoverOverlapData : DiskOverlapData` from **Montel's** chart cover (NOT `ChartDiskCover`: Montel's
nested `innerShrunkChart ⊆ chartOpen ⊆ source` gives a genuine COVERING shrinking; `Finset.equivFin`
reindex keeps `J : Type 0`). `Uov(a,b)` = chart-image of `chartOpen a ∩ chartOpen b`; `Kov(a,b)` =
chart-image of `innerShrunkChart a ∩ innerShrunkChart b` (compact ⊆ Uov, non-convex). Reusable atoms:
`isOpen_chartImage_of_subset_source`, `isCompact_chartImage_of_subset_source` (per-overlap facts the
cochain map needs), `iUnion_innerShrunkChart_coverCenter_eq` (covering, for `leray`).

**Honest distance check:** `exists_cechModel` now needs (geometry ✅): the cochain map
(`Π_p holoSectionToBddHol`, using the geometry's `isOpen/isCompact_chartImage` atoms) → the
`Coboundaries` δ-complex → the `leray` field (disk atoms `dbar_solvable_ball`) → the `cechH1≃supH1`
comparison (germ↔BddHol ∘ Leray K-refine). The wall is far but the front (FA spine · K-bridge · non-convex
compactness · geometry) is all sorry-free. ⚠ Geometry-agent flag: the `leray` ∂̄-solve is on a *ball*, but
`Uov` = chartOpen-overlap-image (open, not a ball) — the assembly will want a ball `⊆ Uov` refinement.
**NEXT executable step = the cochain map + `Coboundaries` δ-complex.**
