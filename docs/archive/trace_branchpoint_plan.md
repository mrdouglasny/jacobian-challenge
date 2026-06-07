# Plan — discharge #4 `traceExtendsAt_branchPoint` (the trace's branch-point extension)

## ✅ DISCHARGED (2026-05-31) — `traceExtendsAt_branchPoint`, `exists_traceForm`, `traceForm` are AXIOM-CLEAN

`#4` is **complete**. `traceExtendsAt_branchPoint`, `traceLocalCoeff_mul_sub_tendsto_zero`, and
`exists_traceForm` all verify with axioms `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
The trace's only remaining sorry is the *unrelated* `traceForm_comp` (#5, functoriality).

**The full chain that closed it (no roots-of-unity / Puiseux):**
1. Reformulated the crux: global `BddAbove` (likely false) → local little-o `(z−z₀)·G(z)→0`
   (`traceLocalCoeff_mul_sub_tendsto_zero`), consumed by Mathlib's
   `differentiableOn_update_limUnder_insert_of_isLittleO`.
2. `sub_div_deriv_tendsto_zero` — one-variable heart: `F` analytic, `F w₀=z₀`, not loc const ⟹
   `(F w−z₀)/F'(w)→0`.
3. `traceSummand_inCoordinates_apply_one_eq_ref` — **exact** per-preimage local coefficient
   `= (α's x₀-frame local coeff)/F'(ψ x)` (cotangent-coordinate computation: the `symmL`/
   `(mfderiv f)⁻¹` obstruction factors cancel in the common chart, via
   `TangentBundle.{continuousLinearMapAt,symmL}_trivializationAt = mfderiv` of charts,
   `mfderiv_section_eq_inverse`, `apply_eq_inCoordinates`).
4. `traceSummand_localCoeff_mul_sub_tendsto` — per-preimage growth `→0` (3 + 2 + `continuousAt_localCoeff`).
5. Fibre-sum assembly (`traceLocalCoeff_mul_sub_tendsto_zero_Y`): additivity (`localCoeffLin.map_sum`),
   properness (`properNbhd`/`isProperMap_of_contMDiff`), finite subcover of `f⁻¹ y₀`, ε/(N+1) count.
6. `fibre_ncard_bddAbove_near_branch` — the uniform off-branch fibre-card bound `≤ N`:
   `fibre_ncard_locally_const` (sheet system) + preconnected punctured chart-ball
   (`Set.Countable.isPathConnected_ball_diff_complex`) + `IsPreconnected.constant`.

Everything below is the historical plan; retained for context.

---

**Goal**: for a branch point `y₀ ∈ branchLocus f`, the canonical extension `traceFunExt f α`
is, at `y₀`,
* `ContMDiffAt` as a cotangent-bundle section (`traceTotalSpaceMk (traceFunExt f α)`), **and**
* `ContinuousAt` **in the fixed `y₀`-frame**, i.e. the local coefficient
  `y ↦ traceLocalCoeff (traceFunExt f α) y₀ y` is `ContinuousAt y₀`.

Discharging this is the **single remaining analytic fact** of the trace; everything
downstream (regluing, ℂ-linearity, `exists_traceForm`) is already proven via
`exists_traceForm_of_branchExtension`.

## 2026-05-31 SOUNDNESS REFACTOR — the branch value is now in the fixed frame (DONE)

The prior design defined `traceFunExt` at a branch point as the **raw-operator** limit
`limUnder (𝓝[≠] y₀) (traceFun f α)`, read in the *varying* chart at `y`. That operator is
**provably discontinuous** for a non-trivial tangent bundle (genus ≥ 2 — the
`CotangentCoeff.lean` obstruction), so:
* the raw `limUnder` need not converge (junk value), and
* the old conjunct-2 `ContinuousAt (traceFunExt f α) y₀` (raw operator) and the
  `htendsto` raw-operator convergence used for ℂ-linearity were **unsound** (relied on a
  false convergence). `traceFunExt_branchValue_correct` (which packaged those facts) was the
  isolated design-gap sorry.

**Fix (implemented).** The branch value is now `traceBranchValue f α y₀ := L • id`, where
`L := limUnder (𝓝[≠] (c y₀)) (z ↦ traceLocalCoeff (traceFun f α) y₀ (c.symm z))` is the
chart-pullback removable-singularity limit of the **local coefficient** (trace read in the
*fixed* `y₀`-trivialization). Key new lemmas:
* `tangent_continuousLinearMapAt_center`, `tangent_symmL_center`, `inCoordinates_center_self`:
  the fixed `y₀`-trivialization coordinate change is the **identity at the center `y₀`**
  (`D(chart∘chart.symm)(y₀) = id`). Hence `traceLocalCoeff coeff y₀ y₀ = (coeff y₀) 1`
  (`traceLocalCoeff_center`).
* `traceFunExt_branchValue_correct` (now **PROVEN, no analytic input**): the local coefficient
  of the extension at `y₀` is exactly `L` — a definitional consequence of the center identity
  (`(L • id) 1 = L`).
* `traceFunExt_branchPoint_eq_smul_id`: at a branch point the operator equals
  `(traceLocalCoeff (traceFunExt f α) y y) • id`, turning operator ℂ-linearity into *scalar*
  local-coefficient ℂ-linearity.
* `inCoordinates_apply_one_add/smul`, `traceLocalCoeff_add/smul`: the local coefficient is
  ℂ-linear in the operator value (since `inCoordinates` is `clEquiv ∘ · ∘ clEquiv.symm`).

**Statement changes (soundness-justified).**
* `traceExtendsAt_branchPoint` conjunct 2: `ContinuousAt (traceFunExt f α) y₀` (raw, FALSE)
  → `ContinuousAt (fun y => traceLocalCoeff (traceFunExt f α) y₀ y) y₀` (fixed frame, TRUE —
  the *shadow* of conjunct 1: section `ContMDiffAt` ⟹ local-coeff continuity).
* `exists_traceForm_of_branchExtension` hypothesis `hext` conjunct 2: matched to the above.
  Its ℂ-linearity (`hadd`/`hsmul`) is re-derived **in the fixed frame** via
  `htendstoLC` (local-coefficient convergence, which genuinely holds) + `tendsto_nhds_unique`
  + `traceFunExt_branchPoint_eq_smul_id` — replacing the unsound raw-operator `htendsto`.
* `exists_traceForm`, `traceForm`, and all public API: **unchanged signatures**; off-branch
  agreement `(T α).toFun y = traceFun f α y` for `y ∉ branchLocus f` is preserved verbatim.

**Result.** `traceFunExt_branchValue_correct` and `exists_traceForm_of_branchExtension` are now
`sorryAx`-free; `exists_traceForm`/`traceExtendsAt_branchPoint` carry `sorryAx` *only* via the
one genuine crux `traceLocalCoeff_bddAbove`. Axioms (all four):
`[propext, Classical.choice, Quot.sound, sorryAx]` — no custom axioms.

## What we have
- `traceFunExt f α y := if y ∈ branchLocus f then limUnder (𝓝[≠] y) (traceFun f α) else traceFun f α y`
  (TraceForm.lean:604). So at a branch point the value **is** the punctured-limit.
- `traceFunExt_eventuallyEq_traceFun`: `traceFunExt =ᶠ[𝓝[≠] y₀] traceFun` (TraceForm.lean:636).
- Off-branch **section**-smoothness machinery (TraceForm.lean:642+) — the template to mirror
  at the branch point (chart-coefficient analyticity ⟹ section `ContMDiffAt` via the
  cotangent-hom-bundle).
- `finite_branchLocus_of_nonconstant`, `eventually_notMem_branchLocus`.
- Local normal form `Discharge/Manifold/LocalNormalForm.lean:exists_local_normal_form`
  (`w ↦ wᵉ` model for the map near a ramification point); `AnalyticKthRoot.lean`.
- Off-branch local sheet system (`exists_localSheetSystem`).

## Decomposition

### Phase B — the bridge (tractable; isolates the crux). PROVE `traceExtendsAt_branchPoint`
assuming a clean **local-boundedness** input:

> `traceFun_chart_bounded` : in a chart `c = chartAt ℂ y₀`, the coefficient
> `z ↦ (traceFun f α (c.symm z)) 1 : ℂ` (the value of the 1-form on the basis vector)
> is **holomorphic on a punctured disk** around `c y₀` and **bounded** there.

From that:
1. Mathlib removable singularity — `Complex.differentiableOn_update_limUnder_of_bddAbove`
   / `analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`
   (`Mathlib/Analysis/Complex/RemovableSingularity.lean`) gives an analytic extension whose
   value at `c y₀` is `limUnder`, hence `ContinuousAt` of the coefficient, and analyticity.
2. Lift through the chart + the cotangent-hom-bundle (`contMDiffAt_hom_bundle`, mirror the
   off-branch machinery at TraceForm.lean:642+) to get the section `ContMDiffAt`.
3. `traceFunExt = limUnder` at `y₀` (def) matches the removable extension's value, so both
   conjuncts transfer from `traceFun` to `traceFunExt` via `traceFunExt_eventuallyEq_traceFun`.

**Deliverable:** `traceExtendsAt_branchPoint` proven *modulo* `traceFun_chart_bounded`
(sorry-split: the bridge is done, the analytic crux is isolated and crisply stated).

### Phase A — the analytic crux (hard; the genuine frontier). PROVE `traceFun_chart_bounded`.
Near `y₀` with ramification orders `eᵢ` on the colliding sheets, in a chart `z`:
- **A1** local normal form: each ramified sheet is `w = ζ^k z^{1/e}` (e branches of `z^{1/e}`)
  via `exists_local_normal_form` + `AnalyticKthRoot`.
- **A2** the trace = `∑` over sheets of `(α(sheet) ∘ mfderiv sheet)`; in coordinates the
  per-sheet term is `(1/e) ∑ₙ aₙ ζ^{k(n+1)} z^{(n+1)/e - 1}` where `α = (∑ₙ aₙ wⁿ) dw` locally.
- **A3** roots-of-unity cancellation: `∑ₖ ζ^{k(n+1)} = e·[e ∣ n+1]`, so summing over `k`
  kills every term except `n+1 = e·m`, leaving `∑_{m≥1} a_{em-1} z^{m-1}` — a **holomorphic**
  power series in `z` (no negative/fractional powers) ⇒ bounded near `0`, value `a_{e-1}` at `0`.
  (Newton-symmetric-function / Puiseux computation; not in Mathlib or `Discharge/`.)

Split A into A1 (local k-th-root branches), A2 (per-sheet coordinate form), A3 (the
roots-of-unity sum identity + holomorphy of the result). A3's core sum identity
`∑_{k<e} ζ^{km} = e·[e∣m]` is elementary (`Finset.geom_sum_eq` / `rootsOfUnity`); the
work is plumbing it through the per-sheet pullback coordinates.

## 2026-05-31 (later) — LITTLE-O REFORMULATION + ANALYTIC HEART PROVEN

The Phase-A crux was **reformulated and largely discharged**, replacing the
roots-of-unity/Puiseux route (A1–A3 above) with a far simpler one.

**The reformulation (user-approved).** The old `traceLocalCoeff_bddAbove` asserted *global*
`BddAbove` of `|G|` over the whole chart target. That is (a) likely **false** — the chart
codomain need not be relatively compact, so `G` need not be bounded out to `∂ c.target` — and
(b) needlessly hard (it forces the symmetric-function cancellation). Mathlib has a *second*
removable-singularity lemma, `Complex.differentiableOn_update_limUnder_insert_of_isLittleO`,
needing only the **local little-o** `G =o[𝓝[≠] z₀] (·−z₀)⁻¹`, i.e. `(z−z₀)·G(z) → 0`. The crux
is now `traceLocalCoeff_mul_sub_tendsto_zero` (that tendsto), and `traceExtendsAt_branchPoint`
consumes it via the `isLittleO` lemma. **No roots-of-unity, no `zᵉ`-sheets, no Newton symmetric
functions.**

**Why it is now easy.** `‖traceFun f α y‖ ≤ ∑_{x∈f⁻¹y} ‖α x‖·‖(mfderiv f x)⁻¹‖`, and near each
branch preimage the crude per-sheet estimate `|z−z₀|·‖(mfderiv f x)⁻¹‖ = |F(w)−z₀|/|F'(w)| → 0`
(triangle inequality only). The cancellation that the Puiseux route extracted by hand is *not
needed* for the little-o.

**Proven this pass (all axiom-clean, `lake build Jacobians.TraceForm` green):**
- `sub_div_deriv_tendsto_zero` — the **one-variable analytic heart**: for `F` analytic at `w₀`,
  `F w₀ = z₀`, not locally constant, `(F w − z₀)/F'(w) → 0` as `w → w₀`. Via `F − z₀ =
  (w−w₀)^(d+1)·g` (`g w₀ ≠ 0`) the ratio is `(w−w₀)·g/((d+1)g + (w−w₀)g') → 0`.
- The crux reduction: `traceLocalCoeff_mul_sub_tendsto_zero` (the `z`-statement) is proven from
  the `Y`-statement `traceLocalCoeff_mul_sub_tendsto_zero_Y` by composing with `c.symm`
  (`Tendsto c.symm (𝓝[≠] z₀) (𝓝[≠] y₀)`), fully proven.

**One isolated `sorry` remains — `traceLocalCoeff_mul_sub_tendsto_zero_Y`** (the manifold side):
`(c y − c y₀)·traceLocalCoeff (traceFun f α) y₀ y → 0` as `y → y₀`.

### ⚠ CORRECTION (2026-05-31, adversarial subagent check) — the naive decomposition was UNSOUND

The earlier "norm bound `‖traceLocalCoeff coeff y₀ y‖ ≤ B·‖coeff y‖` (uniform `B`)" step is
**mathematically false**. A free `∀ φ` bound is *equivalent* to local boundedness of the
bare-fibre coordinate `symmL(tangentTriv y₀) y 1`, which is exactly the genus≥2 obstruction
(`CotangentCoeff.lean` `const_one_section_continuous_of_coordChange_fixes_one`): the constant
native-frame section is discontinuous, and there is **no Riemannian metric on `TY`** (so no
compactness rescue, and `TangentSpace 𝓘(ℂ) y` carries no `Norm` instance). Confirmed three ways
by the subagent (`fun_prop` fails; `continuousAt_hom_bundle` reduces it to the obstruction; only
the *total-space* section is continuous, with no continuous bare-fibre extraction). **So one must
not split the `inCoordinates`/`symmL` factor off the operator norm.**

### Corrected approach — exact per-preimage local coefficient (no missing math)

The `symmL` and `(mfderiv f x)⁻¹` factors **cancel** when the application
`inCoordinates(…)(traceSummand f α x) 1` is kept together and computed exactly in ONE fixed
chart. Off-branch `traceLocalCoeff (traceFun f α) y₀ y = ∑_{x∈f⁻¹y} inCoordinates(…)(traceSummand
f α x) 1` (additive). Each term equals **`a(w)·S'(z)`** where `S = chart_X ∘ s ∘ c.symm` is the
local section in charts, `z = c y`, `w = S(z)`, `a` = `α`'s `chart_X`-coefficient; since `S = F⁻¹`
for `F = c∘f∘chart_X.symm`, `S'(z) = 1/F'(w)`, so the term is `a(w)/F'(w)` — *no `symmL` factor*.
Then `(z−c y₀)·a(w)/F'(w) = a(w)·(F(w)−c y₀)/F'(w) → 0` by `sub_div_deriv_tendsto_zero` (PROVEN).
The exact value comes from `apply_eq_inCoordinates` (CotangentCoeff) + the operator identity inside
`contMDiffAt_pullback_section` (`inCoordinates(sheetPullback) = inCoordinates_X(α) ∘
inCoordinates(mfderiv s)`), evaluated at `1`; the chart-matrix of `mfderiv f x` from `chartAt x`
to `c = chartAt y₀` is `F'(w)` (= `mfderiv (c∘f) x 1` by the proven bridge below).

**PROVEN foundations (in `TraceForm.lean`, commit `10fc1d0`):**
- `norm_inverse_clm`: `‖T.inverse‖ = ‖T 1‖⁻¹` on `ℂ →L[ℂ] ℂ` (unconditional).
- `mfderiv_apply_one_eq_deriv_chartPullback`: `mfderiv h x 1 = deriv (h ∘ chart.symm) (chart x)`
  for `h : X → ℂ` (the `LineIntegral.lean :: h_mfderiv` pattern, target = model space `ℂ`).

**Remaining:** (1) the exact per-preimage value `inCoordinates(…)(traceSummand f α x) 1 = a(w)/F'(w)`
(the cotangent-coordinate computation — the real work), (2) the assembly: properness
(`X` compact ⟹ `f⁻¹W ⊆ ⋃_j U_j`) + uniform off-branch fibre cardinality (`= deg f`).

(The pre-existing #5 sorry `traceForm_comp` is unrelated to this plan and untouched.)

Refs: Forster §10 (the trace), §4.22–4.25 (local normal form `wᵉ`); Griffiths–Harris Ch.2 §2.7.
