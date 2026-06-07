> **✅ DISCHARGED — 2026-06-07 (PR #96).** This axiom is now a proved theorem; this plan is retained as a historical record of the route, not active work. Canonical status: `AXIOM_AUDIT.md` → "Recently discharged".

# `AX_HyperellipticOneForm_eq_form` — discharge recipe

**Location:** `Jacobians/Axioms/HyperellipticLiouville.lean:260`
**Route:** provable-from-other-axioms &nbsp;&nbsp; **Effort:** 4 &nbsp;&nbsp; **Est:** ~1 focused week, ~300–450 LOC (the chart-origin continuity-extension step adds ~50 LOC on top of the cocycle-propagation skeleton), all in `Jacobians/Axioms/HyperellipticLiouville.lean` plus a small `Form.lean` helper
**Blocked by:** `AX_HyperellipticForm_polynomial_decomposition` (Level 2)

**Statement (verbatim):**
```lean
axiom AX_HyperellipticOneForm_eq_form
    {H : HyperellipticData} [hf : Fact (¬ Odd H.f.natDegree)]
    (form : HolomorphicOneForm (HyperellipticEvenProj H)) :
    ∃ g : Polynomial ℂ,
      g.natDegree < H.f.natDegree / 2 - 1 ∧
      form = HyperellipticEvenProj.hyperellipticForm H g
```

**Why it's an axiom right now:** Per the docstring (`HyperellipticLiouville.lean:230-259`), this is the "surjectivity of `hyperellipticForm`" piece of the genus upper bound and is a direct corollary of Level 2 plus the cross-summand cocycle, both of which are now in good shape (cocycle real for inl_inr at `EvenForm.lean:2119` and for inr_inl at `:2165`). It is axiomatized only so the genus theorem `genus_HyperellipticEven_le` (`:279`) can be stated downstream while waiting on Level 2; once Level 2 lands, this is a cocycle-propagation + chart-coverage + boundary-continuity argument. The bridge from L2 to the chart-local coefficient of `hyperellipticForm H g` is already in-tree as `hyperellipticForm_coeff_projX` (`Form.lean:297`), which makes the recipe quite mechanical.

**Gemini critique addressed:** The earlier draft of this recipe attempted a pure pointwise cocycle propagation. As Gemini 3.1 Pro flagged, that argument has a **fatal logical gap at chart origins `z = 0`**: for any branch-point projY chart or infinity-summand inr chart, the chart-transition map to a neighbouring affine projX chart is undefined at the chart origin (the branch / infinity point itself), so `z = 0` is *not* in the source of the transition map, and the cocycle identities `EvenForm.lean:2119` / `:2165` (which require `(extChartAt _ x).symm z ∈ (extChartAt _ y).source`, hence `z ≠ 0` in these cases) cannot be applied there. The pointwise `funext q z` strategy therefore leaves the singleton fibre `{0}` unprovable. The fix is a **boundary-point continuity extension** (new Step 6 below): the cocycle quartet proves `form.coeff q = form'.coeff q` on the *punctured* chart target `target \ {0}`, and analyticity of both sides on the *full* target (which the L1 / `IsHolomorphicOneFormCoeff` predicate `OneForm.lean:69-71` already supplies via `AnalyticOn ℂ (form.coeff q) (extChartAt … q).target`) lets us extend equality across the puncture. The critique also noted that the earlier Step 4 (`inl_inl` propagation) was **redundant** — Step 1 below (from L2) already supplies projX-target equality at *every* `a ∈ smoothLocusY` directly, so no further `inl_inl` cocycle hop is required. That redundant step has been removed.

**Proof recipe**

This is the demo recipe shape: cite L2 + the cross-summand cocycles at `EvenForm.lean:2119, :2165` (the same-summand cocycles at `:272, :310` remain available but are unused after restructuring), close the punctured chart targets, then extend across each chart origin by analytic / continuous extension, and finish with `ext_of_coeff`.

1. **Extract the L2 polynomial.** Apply `AX_HyperellipticForm_polynomial_decomposition` (`HyperellipticLiouville.lean:215`) to `form`, obtaining `g : Polynomial ℂ`, `hDeg : g.natDegree < H.f.natDegree / 2 − 1`, and the projX chart-local identity
   ```
   form.coeff q z = g.eval z / (squareLocalHomeomorph a hpY).symm (H.f.eval z)
   ```
   for **every** `a ∈ smoothLocusY`, every `q` with `Quotient.out q = Sum.inl a`, every `z` in the projX chart target. (Note: L2 is universally quantified over `smoothLocusY` representatives, so projX-side equality at *all* such `q` is in hand directly — no `inl_inl` propagation is needed.)

2. **Define the candidate form.** Let `form' := HyperellipticEvenProj.hyperellipticForm H g` (`Form.lean:104`). It is a real holomorphic 1-form (after the S5 cocycle discharge: `EvenForm.lean:2119, :2165`), and in particular `form'.coeff` is `AnalyticOn ℂ` on every chart target (via the `IsHolomorphicOneFormCoeff` slot of `holomorphicOneFormSubmodule`, `OneForm.lean:69-71, :118-121`).

3. **Match on projX at smoothLocusY points (pointwise, on full target).** The bridge lemma `hyperellipticForm_coeff_projX` (`Form.lean:297`) reads off precisely
   ```
   (hyperellipticForm H g).coeff q z = g.eval z / (squareLocalHomeomorph a hpY).symm (H.f.eval z)
   ```
   under the same hypotheses as Step 1. Combining: `form.coeff q z = form'.coeff q z` whenever `Quotient.out q = Sum.inl a`, `a ∈ smoothLocusY`, and `z ∈ projX_target a` — for **all** such `z`, including the chart origin (the affine projX charts have no removable hole — the branch / infinity points sit on the projY / inr summands, not the inl summand, when `a ∈ smoothLocusY`).

4. **Punctured-target equality on projY (branch-point) charts via inl_inr cocycle.** For a branch point `a ∈ smoothLocusX \ smoothLocusY` covered by a projY chart with `Quotient.out q = Sum.inl a`, use `hyperellipticEvenCoeff_cocycle_inl_inr` (`EvenForm.lean:2119`) to transport the equality of Step 3 from a neighbouring projX chart (at some `a₀ ∈ smoothLocusY` whose projX target overlaps the punctured projY target at `a`) to the projY chart over `a`. The cocycle holds because both `form` and `form'` carry `SatisfiesCotangentCocycle` (the second factor of `holomorphicOneFormSubmodule`, `OneForm.lean:120`). This yields `form.coeff q z = form'.coeff q z` for **every `z ∈ projY_target a` with `z ≠ 0`** — i.e. on the *punctured* projY target, since the cocycle's `(extChartAt _ q).symm z ∈ (extChartAt _ q₀).source` premise (the projX-source membership at `a₀`) fails exactly at the branch point preimage `z = 0`.

5. **Punctured-target equality on inr (infinity) charts via inr_inl and inr_inr cocycles.** For an infinity-summand class `q` with `Quotient.out q = Sum.inr b`, two cocycle hops chain back to Step 3:
   - `hyperellipticEvenCoeff_cocycle_inr_inl` (`EvenForm.lean:2165`) transports equality from the projX side at a neighbouring `a₀ ∈ smoothLocusY` to the inr chart over `b`, on the punctured target.
   - Where two inr charts at `b, b'` overlap, `hyperellipticEvenCoeff_cocycle_inr_inr` (`EvenForm.lean:310`) extends equality across the overlap (likewise punctured at chart origins).

   The four-case dispatch is exactly the one already wired up at `EvenForm.lean:2211-2221`. This exhausts all chart pairs `(inl, inl)`, `(inl, inr)`, `(inr, inl)`, `(inr, inr)` *on the punctured chart targets*. The remaining hole — equality at the chart origin `z = 0` for branch and infinity charts — is closed in Step 6.

6. **Extend across the chart origin by continuity (the boundary-point step).** This step closes the singleton hole `{0}` at every branch / infinity chart origin. For each `q` with `Quotient.out q = Sum.inr b` (or `Sum.inl a` with `a ∉ smoothLocusY`, the branch-point projY case):
   - Both `form.coeff q` and `form'.coeff q` are `AnalyticOn ℂ` on the full chart target `T := (extChartAt 𝓘(ℂ, ℂ) q).target` (from `IsHolomorphicOneFormCoeff`, `OneForm.lean:69-71`). In particular both are **continuous** on `T`, which contains `0` as an interior point.
   - Steps 4–5 give `form.coeff q z = form'.coeff q z` for all `z ∈ T \ {0}`.
   - The punctured neighbourhood `T \ {0}` is dense in `T` near `0` (in fact `0` is in the closure of `T \ {0}` because `T` is open in `ℂ` and `{0}` has empty interior in `ℂ`).
   - Apply a continuity-extension lemma to extend the equality across `0`. Two compatible Mathlib routes:
     - **Preferred (analytic identity principle):** `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` (or `AnalyticOn.eqOn_of_preconnected_of_frequently_eq`) on the connected open chart target: equality on the open dense subset `T \ {0}` forces equality on all of `T`.
     - **Alternative (raw continuity):** `ContinuousAt.tendsto` for both sides at `0`, combined with `Filter.Tendsto.unique` / `Continuous.eq_of_eventually_eq` applied to the `EventuallyEq` witnessed by punctured-target equality in `nhdsWithin 0 (T \ {0}) ≤ nhds 0`. Mathlib lemma name: `Continuous.eq_of_eventually_eq` (no exact-line cite needed; standard Mathlib).
   - Conclude `form.coeff q 0 = form'.coeff q 0` and hence `form.coeff q z = form'.coeff q z` for **every** `z ∈ T`.

   Budget: ~50 LOC for the extension lemma + its two case applications (one for the branch-point projY charts, one for the inr charts). If reused at more than two call sites, factor as a small project lemma `HolomorphicOneForm.eq_of_eqOn_punctured_target` in `OneForm.lean` taking two forms, a point `q`, and an `EqOn` hypothesis on `T \ {0}`, returning `EqOn` on `T`; the analytic-identity-principle proof is ~15 LOC.

7. **Off-target zero from `IsZeroOffChartTarget`.** Both `form` and `form'` are members of `holomorphicOneFormSubmodule` (`OneForm.lean:118`), so both satisfy `IsZeroOffChartTarget` (`OneForm.lean:107-109`). Outside the chart target at any `q`, `form.coeff q z = 0 = form'.coeff q z` trivially. Combined with Steps 3 + 6 (chart-target equality on every `q`), this gives `form.coeff q z = form'.coeff q z` for all `q : HyperellipticEvenProj H`, `z : ℂ`.

8. **Close with `ext_of_coeff`.** Steps 3–7 give `form.coeff = form'.coeff` as a function `HyperellipticEvenProj H → ℂ → ℂ`. Apply `HolomorphicOneForm.ext_of_coeff` (`OneForm.lean:182`) to conclude `form = form' = hyperellipticForm H g`. Together with `hDeg` from Step 1, this is the required witness.

Tactic sketch (final shape):
```lean
theorem AX_HyperellipticOneForm_eq_form
    {H : HyperellipticData} [hf : Fact (¬ Odd H.f.natDegree)]
    (form : HolomorphicOneForm (HyperellipticEvenProj H)) :
    ∃ g : Polynomial ℂ,
      g.natDegree < H.f.natDegree / 2 - 1 ∧
      form = HyperellipticEvenProj.hyperellipticForm H g := by
  obtain ⟨g, hDeg, hL2⟩ := AX_HyperellipticForm_polynomial_decomposition form
  refine ⟨g, hDeg, ?_⟩
  set form' := HyperellipticEvenProj.hyperellipticForm H g with hform'
  apply HolomorphicOneForm.ext_of_coeff
  -- Pull the `funext` over `q` only; defer the `z`-quantifier so we can
  -- separate the punctured-target case (Steps 3–5) from the origin (Step 6).
  funext q
  -- Show coeffs agree as functions ℂ → ℂ for this `q`.
  ext z
  rcases hOut : Quotient.out q with a | b
  · by_cases hpY : a ∈ HyperellipticAffine.smoothLocusY H
    · -- projX side at a smoothLocusY representative: Step 3, no puncture needed.
      by_cases hz : z ∈ (HyperellipticAffine.affineChartProjX a hpY).target
      · rw [hL2 a hpY q hOut hz,
            hyperellipticForm_coeff_projX (H := H) hDeg hpY hOut hz]
      · -- Step 7: off-target ⇒ both zero.
        have h1 := form.2.2.2 q z (by simpa [hOut] using hz)
        have h2 := form'.2.2.2 q z (by simpa [hOut] using hz)
        simp [h1, h2]
    · -- Branch-point projY case (Step 4 on punctured target + Step 6 at origin).
      by_cases hz : z ∈ (extChartAt 𝓘(ℂ, ℂ) q).target
      · -- Inside chart target. Split on z = 0 vs z ≠ 0.
        by_cases hz0 : z = 0
        · -- Step 6: boundary-point continuity extension.
          subst hz0
          exact eq_at_origin_of_eqOn_punctured form form' q
            (eqOn_punctured_branch hL2 hDeg hOut hpY)
        · -- Step 4: one inl_inr cocycle hop at z ≠ 0.
          exact eqOn_punctured_branch hL2 hDeg hOut hpY ⟨hz, hz0⟩
      · -- Step 7: off-target.
        have h1 := form.2.2.2 q z hz
        have h2 := form'.2.2.2 q z hz
        simp [h1, h2]
  · -- Infinity-summand case (Step 5 on punctured target + Step 6 at origin).
    by_cases hz : z ∈ (extChartAt 𝓘(ℂ, ℂ) q).target
    · by_cases hz0 : z = 0
      · subst hz0
        exact eq_at_origin_of_eqOn_punctured form form' q
          (eqOn_punctured_infty hL2 hDeg hOut)
      · -- Two cocycle hops: EvenForm.lean:2165 then (if needed) :310.
        exact eqOn_punctured_infty hL2 hDeg hOut ⟨hz, hz0⟩
    · have h1 := form.2.2.2 q z hz
      have h2 := form'.2.2.2 q z hz
      simp [h1, h2]
```
The `eqOn_punctured_branch` / `eqOn_punctured_infty` helpers are the cocycle-hop calls of Steps 4 / 5 (each ~30–40 LOC, applying `hyperellipticEvenCoeff_cocycle_inl_inr` at `EvenForm.lean:2119`, `_inr_inl` at `:2165`, and where needed `_inr_inr` at `:310`). The `eq_at_origin_of_eqOn_punctured` helper is the Step-6 boundary-extension lemma (~15 LOC if proved via the analytic identity principle, ~50 LOC if proved via raw continuity + filter manipulation; it takes the two analytic functions and an `EqOn` hypothesis on the punctured chart target and returns equality at the origin).

**Files touched**
- `Jacobians/Axioms/HyperellipticLiouville.lean` — replace `axiom AX_HyperellipticOneForm_eq_form` (line 260) with the assembled `theorem`. The body of `genus_HyperellipticEven_le` (line 279) needs no change — it already calls the symbol by name.
- `Jacobians/RiemannSurface/OneForm.lean` — add the small project lemma
  `HolomorphicOneForm.eq_of_eqOn_punctured_target` (or
  `eq_at_origin_of_eqOn_punctured`) packaging the analytic-identity-principle
  boundary extension. Cleanest home is right after `ext_of_coeff` (`:182`),
  before `end HolomorphicOneForm` at `:186`.
- *(Optional helper)* `Jacobians/ProjectiveCurve/Hyperelliptic/Form.lean` — if the cocycle-hop in the projY / infinity-summand cases is reused, factor it out as a `lemma hyperellipticForm_coeff_projY` mirroring `hyperellipticForm_coeff_projX` (`Form.lean:297`).

**Acceptance**
- `lake build Jacobians.Axioms.HyperellipticLiouville` succeeds.
- `#print axioms genus_HyperellipticEven_le` (`HyperellipticLiouville.lean:279`) no longer lists `AX_HyperellipticOneForm_eq_form` (it will still list `AX_HyperellipticForm_polynomial_decomposition` unless L2 also discharged).
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1.

**Risk / escalation triggers**
- If the analytic-identity-principle route in Step 6 cannot be discharged from the existing `IsHolomorphicOneFormCoeff` slot (e.g. because the chart target is not preconnected, or because Mathlib's `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` requires a `Set.EqOn` on a neighborhood with stronger filter hypotheses than `nhdsWithin 0 (T \ {0})` supplies), fall back to the raw-continuity route (`Continuous.eq_of_eventually_eq` + density), and escalate if even that requires a new project-level continuity-of-coefficient lemma.
- If the cocycle-hop bookkeeping in Steps 4–5 needs a branch-point witness `a₀ ∈ smoothLocusY` adjacent to a given branch / infinity point and such an `a₀` is not guaranteed by the existing branch-locus-finiteness infrastructure, the fallback `hyperellipticForm_eq_of_agree_at_affine_smoothX` (`Form.lean:268`) shows the right shape; if porting it to `form = form'` (rather than `g = g'`) requires more cocycle infrastructure than is in `EvenForm.lean`, escalate.
- If after L2 lands, the L2 statement's quantifier shape (it asserts the chart-local identity only on the projX-chart target, not off-target) turns out to interact badly with the punctured-vs-full target split in Steps 3–6, escalate: this needs a one-paragraph extension to the L2 axiom rather than a workaround here.

---
**Vetting trail.** Critique: `_vetting/AX_HyperellipticOneForm_eq_form.md`. Verdict: revise. Revised: 2026-06-03.

**Cross-plan patch (2026-06-03):** Standardised manifold-model-space notation to `𝓘(ℂ, ℂ)` (Mathlib's `modelWithCornersSelf ℂ ℂ`); the single-arg alias `𝓘(ℂ)` caused typeclass-unification failures between generic and concrete plans.
