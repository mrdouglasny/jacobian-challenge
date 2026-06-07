# Preimage-cycle lift — completion plan

Continuation plan for `exists_preimageCycle_of_off_branchLocus`
(`Jacobians/TracePullback.lean`), the geometric heart of the Jacobian
pushforward∘pullback = degree identity. This is the "§3 / loop-lifting machinery"
referenced throughout the codebase. Written 2026-05-30 after sub-piece A landed.

## ⇒ STATUS (2026-05-30, latest): ALL THREE LEAVES PROVEN — the §3 geometric heart is DONE

Leaf A+B `exists_monodromyLiftFamily` is now **proven, sorry-free + axiom-clean**
(`[propext, Classical.choice, Quot.sound]`), commit `990f9f6`. With leaves D & E
already done, `exists_preimageLoopFamily` has **no remaining §3 sorry**: its only
`sorryAx` is the *inherited* branch-point extension `traceExtendsAt_branchPoint`
(through `traceFormTotal`/leaf D), a separate frontier item — NOT the §3 lift geometry.

How A+B was closed (all the analytic infra was already in place; this was the geometry):
* **lift `velCont`** — extended `exists_smoothLift_flatEnd_off_branchLocus` to also yield
  `velCont` (hence a full `IsSmoothPath`). Two new helpers: `velCont_flatEndReparam` (δr's
  velCont via `velCont_reparam`) and `velsection_eventuallyEq_of_eventuallyEq` (velocity-section
  germ invariance — paths agreeing near `t₀` have equal velsections near `t₀`; handles the
  dependent `Bundle.TotalSpace.mk'` transport cleanly since `TangentSpace 𝓘(ℂ) · = ℂ`). The
  velCont proof: interior `(0,1)` via `velContWithinAt_compOn` + `Γ =ᶠ g∘δr`; seam-flat endpoints
  `{0,1}` via `isSmoothPath_const` + germ-invariance congr. (`velContWithinAt_compOn` was moved
  upstream of the lift lemma so it is in scope.)
* **`fibre_inj`** — `lift_eqOn_Icc_of_eq` (new): two lifts of the same off-branch base path
  agreeing at one time agree on `[0,1]`, via a clopen equalizer in the connected subtype
  `↥(Icc 0 1)` (`IsClopen.eq_univ` + `isPreconnected_iff_preconnectedSpace`; open by local
  injectivity off `criticalSet`). Then `enum`-injectivity of the basepoints.
* **`fibre_surj`** — off-branch fibre cardinality constancy: `t ↦ (f⁻¹{δr t}).ncard` is locally
  constant (over each `LocalSheetSystem` base the fibre is the range of the injective sheet map,
  so card `= S.n`), hence constant on connected `[0,1]` (`IsPreconnected.constant`, ℕ discrete via
  `tendsto_pure`+`pure_le_nhds`), value `n` at `0`. Injective-into-equal-card (`Set.eq_of_subset_of_ncard_le`).

Everything below is the prior derivation, retained as historical record.

## ⇒ STATUS (2026-05-30, later): DECOMPOSED into 3 typechecking leaves + PROVEN assembly

`exists_preimageLoopFamily` is now **proven from three leaf lemmas** (assembly compiles,
sorry-free); the geometric heart is bottomed-out. Commit `dc3386c`. The new interface +
leaves live in `TracePullback.lean` just above `exists_preimageLoopFamily`:

* **`MonodromyLiftFamily f δ`** (struct) — the interface: a finite family of seam-flattened
  smooth lifts `Γ i` of `δr = δ∘flatEndReparam` whose time-`t` values `i ↦ Γ i t` sweep the
  fibre `f⁻¹(δr t)` **bijectively** for every `t∈[0,1]`. Fields: `n`, `Γ`, `smooth` (each an
  `IsSmoothPath`, i.e. carries velCont), `velZero_zero/one`, `lifts` (`f∘Γi = δr` on `[0,1]`),
  `fibre_inj`, `fibre_surj`.
* **leaf A+B `exists_monodromyLiftFamily`** — construct it off-branch (one velCont lift per
  fibre point; `fibre_inj` by lift uniqueness/clopen; `fibre_surj` by off-branch fibre-card
  constancy on connected `[0,1]` via the local sheet system). Hardest leaf.
* **leaf D `lineIntegral_traceFormTotal_eq_sum_periodVec`** — projection formula
  `∫_δ trace(ωⱼ) = ∑ᵢ periodVec(Γᵢ)ⱼ`. **KEY SIMPLIFICATION**: the old segment-partition /
  sheet-reassembly / index-matching route is *abandoned* in favour of a single **pointwise
  fibre-sum identity** `traceFun f ωⱼ (δr t)(δr' t) = ∑ᵢ ωⱼ(Γᵢ t)(Γᵢ' t)` — the trace
  fibre-sum reindexed by the time-`t` bijection, each summand `= ωⱼ(Γᵢ t)((mfderiv f)⁻¹ δr' t)`
  with `(mfderiv f)⁻¹(δr' t) = pathSpeed Γᵢ t` (since `f∘Γᵢ = δr`). Integrate; done. No
  `exists_nbhd_cover`/`lineIntegral_pullback_section` partition bookkeeping needed.
* **leaf E `exists_orbitLoops_of_monodromyLiftFamily`** — group lifts into closed smooth loops
  along σ-orbits (`σ` = `fibre`-bijection at `t=1`; iterated `concat`, junctions `0`), account
  both periods (`coeffs=1`, `sheets=M.n`).

### Progress (2026-05-30): leaves D & E DONE; only A+B remains

* **leaf D** — PROVEN, axiom-clean (commit `5a09adc`). `lineIntegral_traceFormTotal_eq_sum_periodVec`
  via the pointwise fibre-sum identity (two private helpers: `traceSummand_lift_velocity_interior`,
  `traceForm_apply_eq_sum_lift_interior`). The `sorryAx` it reports is inherited from
  `traceFormTotal` (open `traceExtendsAt_branchPoint`), NOT new.
* **leaf E** — PROVEN, axiom-clean (commits `b8d264d` helpers, `3ff405d` accounting).
  Orbit machinery: `IsSmoothPath.comp`, `concatPow`(+`_isSmoothPath`/`_periodVec`),
  `comp_concatPow_periodVec`, `periodVec_comp_lift`, `exists_monodromyPerm`,
  `perm_pow_orderOf_cycleOf_apply_self`, `perm_pow_apply_injOn`, and the key
  `exists_orbitCoeff` (orbit-partition accounting: orbit = SameCycle class = image of
  `k↦σ^k i`; `Finset.sum_fiberwise` over the orbit-min representative). orbit loop =
  `concatPow (orderOf(cycleOf i) - 1) i`.

### Leaf A+B remainder (`exists_monodromyLiftFamily`) — the ONLY open piece of the heart

`velContWithinAt_compOn` (pointwise `ContinuousWithinAt` companion of `velCont_compOn`) is
**PROVEN** (commit, axiom-clean) — the analytic crux. Remaining sub-parts (all infra now in place):
1. **`δr` velCont**: `ContinuousOn (velsection (δ∘flatEndReparam)) (Icc 0 1)` via
   `velCont_reparam δ flatEndReparam (deriv flatEndReparam)` — `hmaps`=`flatEndReparam_mem_unit`,
   `hσcont`=`differentiable_flatEndReparam.continuous`, `hσ'cont`=`(Complex.continuous_ofReal.comp
   ((contDiff_flatEndReparam (n:=2)).continuous_deriv …)).continuousOn`, `hspeed`=
   `pathSpeed_flatEndReparam_comp_eq` + `smul_eq_mul`, `hγ`=`hδ.velCont`. (~10 lines, recipe verified.)
2. **lift velCont** (extend `exists_smoothLift_flatEnd_off_branchLocus` — only docstring callers, safe
   to extend its output tuple): `ContinuousOn (velsection Γ) (Icc 0 1)`, 3 cases on `t₀`:
   * `t₀=0`/`t₀=1` (plateau): `Γ ≡ e`/`≡ Γ 1` near the endpoint (reuse `hΓ_const0`/`hΓ_const1`);
     velsection ≡ `⟨e,0⟩`. **Fiddly:** `mk' (Γ s)(pathSpeed Γ s) = mk' e 0` is a *dependent*
     `TotalSpace.mk'` equality (base `Γ s = e`, fibre `pathSpeed Γ s = 0`) — naive `rw [hs]` hits a
     motive error; use `congr 1` (base eq + ℂ-fibre HEq→eq) or `FiberBundle.continuousWithinAt_totalSpace`.
   * interior `0<t₀<1`: `𝓝[Icc] t₀ = 𝓝 t₀`; local two-sided inverse `g` at `Γ t₀` (∉ criticalSet
     since `δ(flatEndReparam t₀)∉branchLocus`), `Γ =ᶠ[𝓝 t₀] g∘δr` (as in
     `differentiableAt_chart_lift_of_notMem_criticalSet`), then `velContWithinAt_compOn` + congr.
3. **construct the family**: fibre `f⁻¹'{δ 0}` finite (`fiber_finite_off_branchLocus (havoid 0)`) ⇒
   `Fintype`; `n=card`, `enum : Fin n ≃ ↥fibre`; `Γ i :=` (extended lift from `(enum i).1`).
   `smooth`/`velZero`/`lifts` fields from the extended lift.
4. **`fibre_inj`**: lift uniqueness — `{s∈Icc | Γ i s = Γ k s}` clopen in connected `Icc`
   (open: local homeo of `f`; closed: T2+cont), nonempty ⇒ `=Icc` ⇒ `Γ i 0 = Γ k 0` ⇒ `i=k`.
5. **`fibre_surj`**: equinumerosity — `t↦#(f⁻¹'{δr t})` locally constant (over each
   `LocalSheetSystem` base `V`, `#fibre = S.n` by `fibre_eq`+`sheet_inj`; `δr` cont) ⇒ constant on
   connected `Icc` ⇒ `=n`; injective (#4) + equal card ⇒ surjective.

All three leaf proofs of D/E were delegated to clean-context agents (statements pinned ⟹ a
sorry-free + axiom-clean build is automatically sound; verify by statement-unchanged + build +
`#print axioms`); leaf E was salvaged from a stopped agent's scratch + completed by hand.
Everything below is the prior derivation (still valid; the C¹ refactor that makes `smooth`/velCont
available, and the reparam-invariance that D/E use).

## ⇒ STATUS (2026-05-30, end of session): ALL ANALYTIC WALLS CLEARED — only the geometry remains

The "DEFINITIVE FINDING" below (loop predicate must be genuinely C¹) is now **DONE**, not pending.
The C¹ refactor is complete + Lean-verified (commits `93b869c` arch-fix → `0500e15` Phase 1 →
`318b8c6` Phase 2; build green, sorry count 71→71, all axiom-clean):
* `IsClosedSmoothLoop`/`IsSmoothPath` now carry `velCont` (continuous velocity tangent-section);
  `….integrable` is a drop-in THEOREM (same signature, derived via the justification lemma), so
  consumers are untouched.
* Full velCont API in `CotangentCoeff.lean` (repointed upstream): `velCont_comp`, `velCont_compOn`
  (`omit [CompactSpace]`, so ℂ can be the source — this is what gives a **local-section lift its
  velCont**), `velCont_reverse`, `velCont_concat`, `velCont_reparam`, `velCont_modelPath`.
* Both analytic facts that were "gated on a Mathlib gap" are cleared: reparam-invariance is proven
  (`periodVec_comp_flatEndReparam`), and the lifts' integrability now follows from `velCont`
  (`velCont_compOn` on the lift `g∘δr` ⇒ `velCont` ⇒ `….integrable`).

**So `exists_preimageLoopFamily` (TracePullback.lean) is the *only* remaining content on this path,
and it needs no further analysis** — only the monodromy permutation (fibre `Fintype` +
`IsCoveringMap.eq_liftPath_iff`) / orbit concatenation (`IsSmoothPath.concat`, junction velocities
zero) / sheet-reassembly projection (`exists_nbhd_cover` + `exists_localSheetSystem_traceForm_eq_sum`
+ `lineIntegral_pullback_section`). Next session: decompose it into precise named sub-lemmas
(bottom out each *statement* first), then prove/delegate. Everything below is preserved as the
historical derivation of WHY the predicate is C¹.

## KEYSTONE (2026-05-30): cotangent-bundle coefficient continuity — **RESOLVED**

The §3 lift integrability (orbit loops being `IsClosedSmoothLoop`) needs control of the
form coefficient along the lift. Resolution (`Jacobians/CotangentCoeff.lean`, sorry-free):
* The **global** coefficient `x ↦ α.toFun x (1 : TangentSpace 𝓘(ℂ) x)` is **FALSE/discontinuous**
  in general — `1 : TangentSpace x` is the `∂/∂z` of the *varying preferred chart*, a
  discontinuous tangent section (obstruction isolated in `const_one_section_continuous_of_coordChange_fixes_one`,
  `target_eq_inCoordinates_of_w`). My earlier "extractor" target was this — it does not exist.
* The **local** coefficient (read in a *fixed* chart/trivialization) **IS continuous and is
  proven**: `continuousAt_inCoordinates`, `continuousAt_localCoeff` (via `contMDiffAt_hom_bundle`:
  the section's smoothness ⇒ its `inCoordinates` rep is continuous into the fixed `ℂ→Lℂ`). This
  is exactly the tool the chart-patchwork needs (and the continuity input `traceForm_comp` needs).

### DEFINITIVE FINDING (2026-05-30, Lean-verified): the loop predicate must be genuinely C¹

"Lemma A" — `IntervalIntegrable (s ↦ α.toFun (γ s)(pathSpeed γ s)) 0 1` from `Continuous γ` +
`IntervalIntegrable (pathSpeed γ) 0 1` (i.e. the velocity-refactor + chart-patchwork plan above) —
**is FALSE** for chart-pointwise-differentiable loops. Verified by isolating three facts:
 * The integrand factors as `c(s)·(pathSpeed γ s)` with `c(s) = α.toFun (γ s) 1` = the **discontinuous,
   unbounded** global coefficient (the very object `CotangentCoeff` shows is discontinuous).
 * In the `inCoordinates` split, `V(s) = (triv).continuousLinearMapAt (γ s)(pathSpeed γ s) = m(s)·pathSpeed γ s`
   with `m(s) = (triv).continuousLinearMapAt (γ s) 1`, and `m∘γ = triv ∘ (constant-1 tangent section)` —
   **discontinuous/unbounded** (the const-1-section obstruction). So `‖(triv).continuousLinearMapAt (γ s)‖`
   is unbounded near `s₀`; "continuous · integrable" never applies. `c = (local coeff)·m`, discontinuity all in `m`.
 * `hγ_speed` only bounds the *moving-chart* velocity; the *fixed-chart* velocity `V = m·pathSpeed` can blow
   up where `γ` accumulates in chart-distorted regions. The conclusion is not derivable from the hypotheses
   (and depends on the `chartAt` assignment of the specific `ChartedSpace`).

The repo's own `IsClosedSmoothLoop`/`IsSmoothPath` carry `integrable` as a **separate field** (alongside
`cont`, pointwise `diff`) for exactly this reason — it is *not* derivable from cont + pointwise-diff.

**Consequence — the genuine fix (the textbook smooth-curve notion the user pointed to from the start):**
the loop predicate must require **honest smoothness**, i.e. a *continuous velocity tangent section* /
`ContMDiffOn 𝓘(ℝ) 𝓘(ℂ) γ (Icc 0 1)` (a real-smooth curve into the complex 1-manifold). From that, the
integrand `α.toFun(γs)(pathSpeed γs)` is **continuous** (curve velocity is a continuous tangent section,
paired with the smooth form), hence `integrable` by `Continuous.intervalIntegrable` — and the seam-fix lift
`g∘δr` (g `C^ω`, δr smooth) is then smooth ⇒ its integrand continuous ⇒ integrable. This is a **deep
foundational refactor** of `IsClosedSmoothLoop`/`IsSmoothPath` (replace `cont`+`diff`+`integrable` with one
`ContMDiffOn`/velocity-continuity field, derive the rest; re-prove ~10 constructors). The bundle local-coeff
lemmas (`CotangentCoeff`) remain useful for the smooth-curve integrand-continuity proof.

*(The earlier "velocity refactor (`speed_integrable`) + chart-patchwork" plan is abandoned — `speed_integrable`
= moving-chart-speed integrability is insufficient; the fixed-chart velocity is what matters, and only genuine
C¹ controls it. This is the third deepening; each was caught before building on a false helper.)*

### C¹ refactor — FOUNDATION PROVEN; concrete plan
**Bottom-out done** (`CotangentCoeff.lean`, sorry-free): `continuousOn_form_pathSpeed` /
`intervalIntegrable_form_pathSpeed_of_velContinuous` — if the **velocity tangent section**
`s ↦ ⟨γ s, pathSpeed γ s⟩` is `ContinuousOn [0,1]` (call this `velCont`), then the integrand
`α.toFun(γs)(pathSpeed γs)` is `ContinuousOn` hence `IntervalIntegrable`, for EVERY `α`. So the new
`velCont` field provably yields the old `integrable` field. (NB the field is the *geometric*
velocity-section continuity, NOT bare-number `pathSpeed` continuity, which leaves the discontinuous
coefficient.)

**Remaining refactor steps** (each large but specified):
 1. In `SmoothPathCore.lean`, replace the `integrable` field of `IsClosedSmoothLoop`/`IsSmoothPath` with
    `velCont : ContinuousOn (fun s => ⟨γ s, pathSpeed γ s⟩ : TangentBundle 𝓘(ℂ) X) (Icc 0 1)`; add a
    derived theorem `.integrable` via `intervalIntegrable_form_pathSpeed_of_velContinuous` (so the ~24
    `.integrable` consumers are unchanged).
 2. Re-prove the ~10 constructors to supply `velCont`:
    - `const`: velocity section ≡ `⟨P,0⟩` (continuous_const).
    - `comp` (`f∘γ`, f global `C^ω`): **clean** — velocity-section(`f∘γ`) `= tangentMap f ∘ velocity-section(γ)`
      (via `pathSpeed_comp_eq_mfderiv`: `pathSpeed(f∘γ)s = mfderiv f(γs)(pathSpeed γs)`), continuous from
      `tangentMap f` continuous (f smooth) + γ's `velCont`. (No base-field issue: `f : X→Y` both complex.)
    - `reverse`/`concat`: velocity-section preserved (junction velocities already 0 for the smooth concat).
    - `ChartBallPath(Smooth)`/`smoothPath(Smooth)`: base velocity-section continuity in a single chart
      (trivialized) — the explicit paths are genuinely C¹.
 3. The §3 seam-fix lift `Γ = g∘δr` (g a *local* `C^ω` section): velCont via the local analogue of `comp`
    (`tangentMap` of the `ContMDiffOn` section on the interior; constant ⟹ `⟨·,0⟩` near the seam ends).
After this, lift loops are `IsClosedSmoothLoop` ⇒ the monodromy/orbit/projection geometry proceeds
(`IsCoveringMap.eq_liftPath_iff`, `IsSmoothPath.concat`, fibre-sum-of-lifts projection).

## Goal

`exists_preimageCycle_of_off_branchLocus (f hf hnonconst) (δ) (hδ : IsClosedSmoothLoop δ)
(havoid : ∀ t, δ t ∉ branchLocus f) : Nonempty (PreimageCycle f hf δ)`.

A `PreimageCycle` bundles: `n`, `loops : Fin n → ℝ → X`, `loops_smooth` (each
`IsClosedSmoothLoop`), `coeffs : Fin n → ℤ`, `sheets : ℕ`, and the two identities
- `pullback_eq : ambientPullbackJac f hf (periodVec δ) = ∑ i, coeffs i • periodVec (loops i)`
- `pushforward_eq : ∑ i, coeffs i • periodVec (f ∘ loops i) = (sheets : ℤ) • periodVec δ`.

## Status

**Top-level theorem `exists_preimageCycle_of_off_branchLocus` is now PROVEN** — reduced
(sorry-free coordinate glue) to the single elementary geometric lemma
`exists_preimageLoopFamily` via the bridge `ambientPullbackJac_periodVec_apply_eq_lineIntegral_traceFormTotal`.
So the ambient/matrix layer of the whole §3 chain is finished; the one remaining sorry
(besides the pre-existing, deferred `exists_loop_off_branchLocus`) is `exists_preimageLoopFamily`,
stated purely in line-integral/period terms.

**Frontier (corrected twice — read carefully).** Reparam-invariance is NOT blocked and
needed no refactor: it is a *monotone change of variables* handled by Mathlib's
measure-theoretic monotone CoV for merely *integrable* integrands
(`integral_image_eq_integral_deriv_smul_of_monotoneOn`, the codebase already uses the
`integrableOn_image_iff` sibling for `smoothStep01`) — DONE sorry-free. **BUT the lift
*integrability* genuinely DOES need a regularity strengthening (the textbook-C¹ direction the
user originally pointed to).** Why: the orbit loops must be `IsClosedSmoothLoop`, whose
`integrable` field for a lift `Γ = g∘δr` (local section `g`) reduces — via the norm bound
`‖ωᵢ(Γ s)(pathSpeed Γ s)‖ ≤ ‖ωᵢ‖∞ · ‖pathSpeed Γ s‖` and `pathSpeed Γ = mfderiv g · pathSpeed δr`
— to **raw `pathSpeed δ` being interval-integrable**. The current `IsClosedSmoothLoop`
provides only the basis-form *pairings* `(periodBasisForm X i)(γ t)(pathSpeed γ t)` integrable,
from which raw `pathSpeed` is NOT recoverable (the basis forms can share zeros). The
`IsClosedSmoothLoop.comp` trick (expand `pullbackForm f` in the *global* basis) does not apply,
because the lift's section `g` is *local* (no global `pullbackForm g`). So lift integrability is
blocked on the weak predicate.

**Recommended fix (textbook-sound, user-pre-approved): add raw velocity integrability to the
loop predicate.** Strengthen `IsClosedSmoothLoop`/`IsSmoothPath` with a field
`speed_integrable : IntervalIntegrable (pathSpeed γ) volume 0 1` (the loop has integrable
velocity — the natural textbook regularity), and *derive* the old basis-pairing `integrable`
from it (`|formᵢ(γt)(pathSpeed γt)| ≤ ‖formᵢ‖∞·‖pathSpeed γt‖`). Then lift integrability follows
by the norm-bound argument **without any cotangent-bundle scalar-coefficient extraction** (only
boundedness of a continuous section over a compact set + `speed_integrable` of `δr` via the
monotone CoV). Cost: the repo-wide predicate refactor (~10 constructors must prove
`speed_integrable`; for the explicit paths `pathSpeed` is continuous hence integrable, so these
are routine). *This re-corrects the over-optimistic "no refactor / no missing math" — that held
for reparam-invariance, not for lift integrability.* The other open pieces (monodromy permutation
`IsCoveringMap.eq_liftPath_iff` + orbit concat `IsSmoothPath.concat`; projection via fibre-sum-of-
lifts `traceFun = ∑ₑ` + `traceForm_toFun_of_notMem_branchLocus`) are genuinely just hard Lean,
and become clean once the loops are `IsClosedSmoothLoop` (i.e. after the `speed_integrable` refactor).

- **A — continuous path-lift: DONE, sorry-free** (`exists_continuous_lift_off_branchLocus`,
  commit `32d435e`). `δ` off-branch lifts through the proven covering via Mathlib's
  `IsCoveringMap.liftPath`, repackaged to `ℝ → X` with `Set.projIcc`. `#print axioms` =
  `[propext, Classical.choice, Quot.sound]`. (Added `import Mathlib.Topology.Homotopy.Lifting`.)
- **B — smoothness of the lift: DONE, sorry-free**
  (`differentiableAt_chart_lift_of_notMem_criticalSet`). A continuous lift `Γ` of `δ`
  through a non-critical point is chart-pullback-differentiable wherever `δ` is.
  Proof exactly as planned: two-sided local inverse `g` at `Γ t₀`, `Γ =ᶠ g∘δ` near `t₀`
  (no lift-uniqueness needed), `G∘d` chart factorization, `g` holomorphic ⇒ `ℝ`-diff via
  `writtenInExtChartAt`+`restrictScalars`. `#print axioms` = `[propext, Classical.choice,
  Quot.sound]`. Compiled essentially first-try (mirrors `IsClosedSmoothLoop.comp`).

## Proven infrastructure to build on

- **Covering**: `isCoveringMap_restrictPreimage_compl_branchLocus` (PeriodLattice) — a genuine
  `IsCoveringMap` of `(univ \ branchLocus f).restrictPreimage f` on subtypes. Mathlib
  `IsCoveringMap.liftPath` / `liftPath_trans` / `liftPath_apply_one_eq_of_homotopicRel`
  (`Mathlib.Topology.Homotopy.Lifting`). NB: `IsCoveringMap` unfolds to a Pi type, so
  dot-notation fails — use explicit `IsCoveringMap.liftPath cov …`.
- **Local sections**: `exists_twoSided_localInverse` (TraceForm.lean) — at any non-critical
  `x₀`, a holomorphic `g` with `f∘g=id` on open `V∋f x₀`, `g∘f=id` near `x₀`, `g(f x₀)=x₀`,
  `g` `C^ω` on `V`. Also `exists_holo_localInverse_of_notMem_criticalSet`, `isLocalHomeoOffCritical`.
- **Fibre finiteness**: `fiber_finite_off_branchLocus` (PeriodLattice) — `(f⁻¹'{y}).Finite` off-branch
  (= the sheet count, classically `deg f`).
- **Line-integral change of variables**: `lineIntegral_pullback` (LineIntegral.lean, PROVEN),
  `periodVec_comp_eq_lineIntegral_pullback`, `periodVec_pushforward` (PeriodLattice).
- **Trace off-branch**: `traceForm_toFun_of_notMem_branchLocus` (TraceForm.lean) — off-branch
  `traceForm = traceFun = ∑ sheets sheetPullback`.
- **Chart chain-rule template**: `pathSpeed_comp_eq_mfderiv` (LineIntegral.lean:492-576) — the
  `chartY ∘ map ∘ chartX.symm` differentiability pattern, to be mirrored in B.

## Remaining steps

### B — smoothness of the lift — **DONE, sorry-free**
`differentiableAt_chart_lift_of_notMem_criticalSet` (TracePullback.lean): given `Γ`
continuous at `t₀`, `∀ᶠ t in 𝓝 t₀, f (Γ t) = δ t`, `Γ t₀ ∉ criticalSet f`, and
`δ` chart-pullback-diff at `t₀`, then `Γ` is chart-pullback-diff at `t₀`. Proof exactly
as the plan predicted (two-sided inverse `g`, `Γ =ᶠ g∘δ`, `G∘d` factorization,
`writtenInExtChartAt`+`restrictScalars`). Compiled essentially first-try. **NB the
hypothesis is `ContinuousAt Γ t₀` + the *eventually* `f∘Γ=δ`** — for A's `projIcc`-clamped
lift this `∀ᶠ` holds only for `t₀ ∈ (0,1)` (open interval), NOT at the endpoints `0,1`,
because outside `[0,1]` the clamped lift is constant while `δ` is not. So **B gives lift
differentiability on `(0,1)` only**; the endpoint/seam differentiability is the C difficulty.

### D-algebra — period-level matrix↔integral bridge — **DONE, sorry-free**
`ambientPullbackJac_periodVec_apply_eq_lineIntegral_traceFormTotal` (TracePullback.lean):
`(ambientPullbackJac f hf (periodVec δ))_i = ∫_δ traceFormTotal f hf (ωᵢ^X)`. Pure linear
algebra + `lineIntegral` linearity, dual to `periodVec_pushforward`. **This reduces
`pullback_eq` to the geometric projection identity** `∫_δ trace(ωᵢ) = ∑_loops coeffs·∫_loop ωᵢ`.

### D-geom infra — local sheet decomposition — **DONE, sorry-free**
`exists_localSheetSystem_traceForm_eq_sum` (TraceForm.lean): off-branch there is a local
sheet system `S` at `y₀` with, for off-branch `y ∈ S.V`,
`(traceForm f hf hnonconst α).toFun y = ∑ᵢ sheetPullback α (S.sheet i) y`. The per-base
input to the projection formula.

### C — seam smoothness **SOLVED, sorry-free**; monodromy/orbit + integrability still open
**Seam-smoothness fix — DONE** (`flatEndReparam` + `exists_smoothLift_flatEnd_off_branchLocus`,
sorry-free, axioms `[propext, Classical.choice, Quot.sound]`). The gating sub-problem the earlier
plan flagged is resolved by a *better choice of reparametrization*: `flatEndReparam` is **constant
near the endpoints** (a genuine plateau, `Real.smoothTransition (2t−1/2)`), NOT merely zero-derivative
like the cubic `smoothStep01`. Lifting `δ ∘ flatEndReparam` from a fibre point `e` then gives a lift
that is literally *constant* near `0,1` (continuity + local injectivity of `f`, using A's now-exposed
`projIcc` clamp facts `Γ≡e on (-∞,0]`, `Γ≡Γ 1 on [1,∞)`) — hence two-sided differentiable with zero
velocity there, with NO one-sided gluing; the interior is plain B. Output: `Γ` continuous, `Γ 0 = e`,
`f(Γ t)=δ(flatEndReparam t)` on `[0,1]`, chart-diff on all `[0,1]`, `pathSpeed Γ 0 = pathSpeed Γ 1 = 0`,
and `f(Γ 1)=δ 0` (monodromy target in the fibre). (A was extended to expose its clamp; no callers broke.)

**Transport/regularity lemmas — DONE, sorry-free:**
 * `lineIntegral_comp_flatEndReparam` / `periodVec_comp_flatEndReparam`: `periodVec (γ ∘
   flatEndReparam) = periodVec γ`, via the measure-theoretic monotone CoV
   (`integral_image_eq_integral_deriv_smul_of_monotoneOn`, no continuity needed). Transports the
   final `PreimageCycle` from `δ∘flatEndReparam` back to `δ` (`PreimageCycle.congr_periodVec`).
 * `lineIntegral_congr_of_eqOn` / `periodVec_congr_of_eqOn`: line integral / period depend only on
   the path's `[0,1]` values (integrand germ agrees on the open interior; endpoints null). Gives the
   single-lift pushforward `lineIntegral α (f∘Γ) = lineIntegral α δr` (since `f∘Γ = δr` on `[0,1]`).
 * `intervalIntegrable_comp_flatEndReparam`: integrability preserved under `flatEndReparam` (the
   *integrability* version of the monotone CoV, mirroring the codebase `smoothStep01` proof) — gives
   `δr`'s basis-integrand integrability from `δ`'s, the input to the lift-integrability patchwork.
 Supporting: `flatEndReparam_{hasDerivAt,monotone,image_Icc}`, `pathSpeed_flatEndReparam_comp_eq`.
 All `#print axioms = [propext, Classical.choice, Quot.sound]`.

**Still open for C (all unblocked — "hard Lean, no missing math"):**
 1. **Lift integrability** — upgrade `exists_smoothLift_flatEnd_off_branchLocus` to a full `IsSmoothPath`.
    Plateau ends give `0`; the middle `[1/4,3/4]` is `Γ = g∘δr` locally ⇒ integrand is a ℂ-combination
    of `δr`-basis integrands, each integrable by `intervalIntegrable_comp_flatEndReparam` (DONE).
    Remaining: the patchwork — a finite cover (`exists_nbhd_cover` with `W x` = a two-sided-inverse
    neighborhood) on which `Γ = g_k∘δr`, the per-segment `pathSpeed_comp` + pullback-form expansion,
    and gluing `IntervalIntegrable` over the partition.
 2. **Monodromy permutation** `σ : F → F`, `σ e = Γ_e 1`, on the finite fibre `F=f⁻¹'{δ 0}`
    (`fiber_finite_off_branchLocus` ⇒ `Fintype`); bijective by lift uniqueness
    (`IsCoveringMap.eq_liftPath_iff` ✓ — found). Package `e ↦ Γ_e` as a function (choice over the fibre).
 3. **Orbit concatenation** into closed loops via `IsSmoothPath.concat` (zero junction velocities ✓
    from the seam fix) + `periodVec_concat_of_smooth`; `n`=#orbits, `coeffs i = 1`, `sheets = card F`.

### D-geom — projection formula (open; infra now all present)
Goal `∫_δ traceFormTotal f hf ωᵢ = ∑_loops coeffs·periodVec(loop)_i` (then `pullback_eq`
via D-algebra). Partition `[0,1]` by `exists_nbhd_cover` (Lebesgue, uniform `k/n` grid) so each
segment `δ|[k/n,(k+1)/n]` lands in some base `S_k.V` (from `exists_localSheetSystem_traceForm_eq_sum`).
On each segment `∫ trace(ωᵢ) = ∑_sheets ∫ sheetPullback = ∑_sheets ∫_{sheet∘δ|seg} ωᵢ`
(`lineIntegral_pullback_section`). **Remaining bookkeeping:** the per-segment sheet pieces
`sheet∘δ|seg` match across segment boundaries (lift continuity/uniqueness) and reassemble into the
global lifts `Γ_e`, then group by `σ`-orbit into the `loops`. This index-matching is the combinatorial
heart shared with C. Off-branch throughout ⇒ **no branch-point continuity needed** (unlike `traceForm_comp`).

### E — pushforward_eq (open; reduces to concat bookkeeping)
`∑ coeffs • periodVec (f ∘ loops) = sheets • periodVec δ`. Each `f∘loop` over an orbit of length
`ℓ` is `δ` traversed `ℓ` times (`f∘Γ_e=δ`); `periodVec(f∘loop)=ℓ•periodVec δ` via
`periodVec_concat_of_smooth`; `∑_orbits ℓ = card F = sheets`.

### F — assemble `PreimageCycle` — **DONE, sorry-free coordinate glue**
`exists_preimageCycle_of_off_branchLocus` reduces to `exists_preimageLoopFamily` via the bridge
(see Status). All of C/D-geom/E/F is now packaged into that one elementary lemma.

## Infrastructure confirmed available (2026-05-30 audit)
All non-monodromy ingredients are proven and the coordinate layer is fully wired in:
A (`exists_continuous_lift_off_branchLocus`, clamp-exposing), B
(`differentiableAt_chart_lift_of_notMem_criticalSet`), the seam fix
(`flatEndReparam` + `exists_smoothLift_flatEnd_off_branchLocus`), the matrix↔integral bridge,
`exists_localSheetSystem`(+`_traceForm_eq_sum`), `exists_nbhd_cover` (partition),
`lineIntegral_pullback_section`, `IsSmoothPath.concat`/`periodVec_concat_of_smooth`,
`fiber_finite_off_branchLocus`, and the proven reduction `exists_preimageCycle_of_off_branchLocus`.
**The sole remaining content is `exists_preimageLoopFamily`: the monodromy/orbit + partition/
reassembly combinatorics, gated on the analytic CoV/regularity gap (see Status (a)/(b)).**

## Separately recorded: `traceForm_comp` is infrastructure-blocked

The other open trace gap, `traceForm_comp` (TraceForm.lean, the `(g∘f)₊ = g₊∘f₊` functoriality
law), is NOT a quick win. Both a density+continuity proof and the `exists_traceForm` framework
need `ContinuousAt` of an opaque `traceForm.choose`'s *coefficient* at branch points — i.e. a
general **cotangent-hom-bundle coefficient-continuity extractor** (`contMDiffAt_hom_bundle`-style,
~40-80 lines of bundle work). Two subagents stalled there. Unlike D above, `traceForm_comp` cannot
avoid branch-point continuity. `traceForm_id` IS done (commit `2c2ad32`) because `branchLocus(id)=∅`.
