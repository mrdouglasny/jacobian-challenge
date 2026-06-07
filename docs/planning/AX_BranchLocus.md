> **✅ DISCHARGED — 2026-06-04 (Phase 1).** This axiom is now a proved theorem; this plan is retained as a historical record of the route, not active work. Canonical status: `AXIOM_AUDIT.md` → "Recently discharged".

# `AX_BranchLocus` — discharge recipe

**Location:** `Jacobians/Axioms/BranchLocus.lean:100`
**Route:** mathlib-now &nbsp;&nbsp; **Effort:** 4 &nbsp;&nbsp; **Est:** ~3 focused days, ~150 LOC (~80 LOC of glue inside `Axioms/BranchLocus.lean` + ~70 LOC of a thin "weighted sum is globally constant" lemma threaded through `Vendor/Wallace/HolomorphicForms/HolomorphicMap.lean`; no Mathlib PR needed)
**Blocked by:** none (the supposed blocker — a manifold-level open mapping theorem — is already discharged inside `Vendor/Wallace/HolomorphicForms/HolomorphicMap.lean` as `weightedFiberConservation_of_contMDiff` at line 1199, which uses Mathlib's complex `Mathlib.Analysis.Complex.OpenMapping` chart-by-chart and bypasses needing a free-standing manifold OMT)

**Statement (verbatim):**
```lean
/-- **Axiom (BranchLocus).** For a non-constant holomorphic map between
compact Riemann surfaces, there's a common degree `d` such that
fiber-sums of `localOrder` all equal `d`, and the branch locus is
finite. -/
axiom AX_BranchLocus {X Y : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X]
    [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ, ℂ) ω Y]
    (f : X → Y) (_hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (_hnc : ¬ ∃ c : Y, ∀ x : X, f x = c) :
    ∃ d : ℕ, 0 < d ∧
      (∀ q : Y, (∑' p : X, localOrder f p q) = d) ∧
      { q : Y | ∃ p : X, f p = q ∧ localOrder f p q > 1 }.Finite
```

**Why it's an axiom right now:** The docstring (`BranchLocus.lean:25–31`) explains: "Mathlib's open-mapping-for-holomorphic-maps infrastructure is specific to ℂ-valued maps, not maps between manifolds." This is half the story — the Wallace vendor module (`Jacobians/Vendor/Wallace/HolomorphicForms/HolomorphicMap.lean`) has *already* solved the manifold-OMT problem chart-locally, calling Mathlib's `AnalyticOnNhd.is_constant_or_isOpenMap` (`Mathlib/Analysis/Complex/OpenMapping.lean:177`) and Mathlib's principle of isolated zeros `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero` (`Mathlib/Analysis/Analytic/IsolatedZeros.lean:125`). The global-degree statement is morally just "the locally-constant function `q ↦ Σ multiplicities` on connected `Y` is globally constant." Load-bearing pieces still missing in the project, all of which are short glue lemmas rather than infrastructure: (a) "local-constancy + connectedness → global-constancy" (Mathlib `IsLocallyConstant.apply_eq_of_isPreconnected` at `Mathlib/Topology/LocallyConstant/Basic.lean:326`, and `LocallyConstant.eq_const` at line 334); (b) packaging the local invariance of `mapAnalyticOrderAt`-weighted Finset sums (`HolomorphicMap.lean:1199`) into a global existential; (c) translating the project-internal `localOrder` (`BranchLocus.lean:69`, which adds the `if f p = q` guard) into the Wallace `mapAnalyticOrderAt` summand (`HolomorphicMap.lean:175`) the Wallace lemmas operate on; (d) replacing `Finset.sum (Finite.toFinset …)` by `tsum` — trivial via `tsum_eq_sum` since `localOrder f p q = 0` outside the (finite) fiber `f⁻¹{q}` once we know fibers are finite.

**Proof recipe**

Following **Forster, *Lectures on Riemann Surfaces*, Ch. I §4 (Theorem 4.24, "the number of preimages, counted with multiplicities, is constant")** and **Miranda, *Algebraic Curves and Riemann Surfaces*, Ch. II §2 (Proposition 2.6 + the discrete-fiber consequences in §4.1)**:

1. **Discharge non-constancy → finite-fiber.** The Wallace module already proves: `isHolomorphic_finite_fiber` (`Jacobians/Vendor/Wallace/HolomorphicForms/HolomorphicMap.lean:648`) gives `(f ⁻¹' {y}).Finite` for every `y : Y` from `IsHolomorphic f` + non-constancy + compact preconnected source + T2 target. Project `ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f` to `IsHolomorphic` via `IsHolomorphic.of_contMDiff`-style constructors used throughout `HolomorphicMap.lean:1199–1366`; concretely the `weightedFiberConservation_of_contMDiff` proof already produces `finite_fiber : ∀ y, (f ⁻¹' {y}).Finite` from the same `ContMDiff` hypothesis, so this step is a name-extraction not a new proof.

2. **Apply weighted-fiber conservation (the heart of the Open Mapping Theorem on manifolds in disguise).** Invoke `weightedFiberConservation_of_contMDiff` (`Jacobians/Vendor/Wallace/HolomorphicForms/HolomorphicMap.lean:1199`). Its hypotheses are `[CompactSpace X] [T2Space X] [PreconnectedSpace X] [T2Space Y]` and `ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f` — all derivable from the axiom signature (`ConnectedSpace → PreconnectedSpace` is `Mathlib`; `ω ≥ ⊤` so `hf.of_le le_top` strips analyticity down to `C^∞`). The conclusion is exactly: for every `y₀ : Y`, the function `Φ : Y → ℕ`, `Φ y := Finset.sum (finite_fiber y).toFinset (mapAnalyticOrderAt f)`, is **eventually equal** to `Φ y₀` near `y₀` — i.e. `Φ` is locally constant.

3. **Promote local-constancy to global constancy via `ConnectedSpace Y`.** Wrap `Φ` as `IsLocallyConstant Φ` (Mathlib `IsLocallyConstant.iff_eventually_const` / direct construction from Step 2). Then apply `IsLocallyConstant.apply_eq_of_isPreconnected` (`Mathlib/Topology/LocallyConstant/Basic.lean:326`) — or, more cleanly, package `Φ` as a `LocallyConstant Y ℕ` and use `LocallyConstant.apply_eq_of_preconnectedSpace` (`Mathlib/Topology/LocallyConstant/Basic.lean:330`) / `LocallyConstant.eq_const` (line 334), both of which need only `PreconnectedSpace Y` (immediate from `ConnectedSpace Y`). Define `d := Φ y₀` for any basepoint `y₀` (exists by `Nonempty Y`, which follows from `ConnectedSpace Y`).

4. **Convert `Finset.sum (toFinset …)` to `tsum`.** With `fib_finite : (f ⁻¹' {y}).Finite` in hand and the fact that `localOrder f p y = 0` whenever `f p ≠ y` (immediate from the `def` at `BranchLocus.lean:69–72` via `if_neg`), the support of `p ↦ localOrder f p y` is contained in the fiber `f ⁻¹' {y}`, which is finite. Hence `∑' p, localOrder f p y = ∑ p ∈ fib_finite.toFinset, localOrder f p y` (Mathlib `tsum_eq_sum_of_ne_finset_zero` or `tsum_eq_sum` on a finite-support function). On the finset, `localOrder f p y = mapAnalyticOrderAt f p` (by the `if_pos` branch of the `def` at `BranchLocus.lean:69–72`, since `p ∈ fib_finite.toFinset ↔ f p = y`). Conclude `∑' p, localOrder f p y = Φ y = d`. This discharges conjunct 1 of the existential.

5. **Positivity `0 < d`.** Take any `x : X` (exists by `ConnectedSpace X ⇒ Nonempty X`), let `y₀ := f x`. Then `x ∈ fib_finite.toFinset` at `y₀`, and `mapAnalyticOrderAt_pos_of_contMDiff hf hnc x` (`HolomorphicMap.lean:884`) gives `0 < mapAnalyticOrderAt f x`. Hence `Φ y₀ ≥ mapAnalyticOrderAt f x ≥ 1`, so `d = Φ y₀ ≥ 1 > 0`. This discharges conjunct `0 < d`.

6. **Finiteness of the branch locus** *(rewritten to fix the point-set gap)*. The set `B := { q : Y | ∃ p : X, f p = q ∧ localOrder f p q > 1 }` equals `f '' { p : X | mapAnalyticOrderAt f p > 1 }` (modulo the `localOrder`/`mapAnalyticOrderAt` translation in Step 4). Reduce to: **`R := { p : X | mapAnalyticOrderAt f p > 1 }` is finite on the compact source `X`.** Then `B = f '' R` is finite by `Set.Finite.image`. To prove `R.Finite`, we **must cover all of `X` by open sets each containing at most one ramified point** (the previous draft erroneously covered only the ramified subset and tried to extract a finite subcover of a subset directly from `CompactSpace X`):

   6a. **Ramified points (`k ≥ 2`).** For each `p ∈ R`, set `k_p := mapAnalyticOrderAt f p ≥ 2`. Apply `local_kfold_ramified_of_contMDiff` (`HolomorphicMap.lean:1082`) at `p` with `k = k_p`: this returns an open neighborhood `U_p ⊆ X` of `p` and an open neighborhood `V_p ⊆ Y` of `f p` such that, for every `y ∈ V_p \ {f p}`, the fiber `f ⁻¹' {y} ∩ U_p` consists of exactly `k_p` simple (order-1) preimages. In particular every point of `U_p \ {p}` is mapped to some `y ≠ f p` and is order-1; so `U_p ∩ R = {p}`. (If the `V_p \ {f p}` window happens to be empty — it isn't, because `Y` is T2 and `V_p` is an open neighborhood — the same conclusion holds via the `(∀ x' ∈ U, f x' = y → x' ∈ s)` clause of `local_kfold_ramified`.)

   6b. **Unramified points (`k = 1`)** *(the gap)*. For each `p ∈ X \ R`, `mapAnalyticOrderAt f p = 1` (since `mapAnalyticOrderAt_pos_of_contMDiff` at line 884 forces `≥ 1`, and `p ∉ R` forces `≤ 1`). Apply `local_kfold_ramified_of_contMDiff` (`HolomorphicMap.lean:1082`) **with `k = 1`**: this returns an open neighborhood `U_p ⊆ X` of `p` and `V_p ⊆ Y` of `f p` such that, for every `y ∈ V_p \ {f p}`, the fiber `f ⁻¹' {y} ∩ U_p` has exactly one element, which is order-1. We may need to shrink `U_p` so that *every* point of `U_p` has order 1 — but actually, the Wallace lemma's exclusivity clause `(∀ x' ∈ U, f x' = y → x' ∈ s)` plus the fact that the single-element `s` lists order-1 preimages already forces every `x' ∈ U_p \ {p}` to be order-1 (and `p` itself is order-1 by hypothesis). So `U_p ∩ R = ∅`. (Equivalent, less indirect formulation: since `mapAnalyticOrderAt f` is upper-semi-continuous in this setting — the chart-local Mathlib `analyticOrderAt` jumps up only on a discrete set by `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero` at `Mathlib/Analysis/Analytic/IsolatedZeros.lean:125` — the set `{p | mapAnalyticOrderAt f p ≥ 2}` is closed, so its complement `X \ R` is open, and any open subset around a point in it lies in `X \ R`. Either route works; the first is preferred since it reuses the same Wallace lemma already cited in 6a.)

   6c. **Form an open cover of all of `X`.** Take `𝒰 := { U_p | p ∈ X }`. By construction `p ∈ U_p`, so `𝒰` covers `X`. Each `U_p` is open.

   6d. **Extract a finite subcover by `CompactSpace X`.** `IsCompact.elim_finite_subcover` (Mathlib, applied to `isCompact_univ`) yields a finite subset `S ⊆ X` with `X ⊆ ⋃ p ∈ S, U_p`.

   6e. **Bound `|R|`.** Each `U_p` for `p ∈ S` contains at most one ramified point: zero if `p ∉ R` (case 6b), exactly `{p}` if `p ∈ R` (case 6a). Hence `R ⊆ { p ∈ S | p ∈ R }`, which is a subset of a finite set; thus `R.Finite` by `Set.Finite.subset`. Then `B = f '' R` is finite by `Set.Finite.image`.

**Next discrete deliverable.** **Step 3: ship a `weightedFiberSum_constant_of_contMDiff` lemma** in `Vendor/Wallace/HolomorphicForms/HolomorphicMap.lean` (between lines 1366 and `end Compatibility`) that combines `weightedFiberConservation_of_contMDiff` (already there, line 1199) with `IsLocallyConstant.apply_eq_of_isPreconnected` (`Mathlib/Topology/LocallyConstant/Basic.lean:326`), giving the clean statement
```lean
theorem weightedFiberSum_constant_of_contMDiff
    [IsManifold 𝓘(ℂ, ℂ) ω X] [IsManifold 𝓘(ℂ, ℂ) ω Y]
    [CompactSpace X] [T2Space X] [ConnectedSpace X]
    [T2Space Y] [PreconnectedSpace Y]
    {f : X → Y} (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (hnc : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) :
    ∃ d : ℕ, ∀ y : Y,
      Finset.sum (isHolomorphic_finite_fiber … hnc y).toFinset
        (mapAnalyticOrderAt f) = d
```
This is ~40 LOC and is the only piece of project infrastructure missing for the rest of the recipe to land as a 4-step tactic block inside `AX_BranchLocus`. It is also reusable by `AX_pushforward_pullback` (ROADMAP line 86) and `pushforwardOneForm` (ROADMAP line 173), making this the highest-leverage single deliverable. Once it lands, replace `axiom AX_BranchLocus` at `BranchLocus.lean:100` with a `theorem` whose body is Steps 4–6 above. No Mathlib PR is required at any point.

**Files touched**
- `Jacobians/Vendor/Wallace/HolomorphicForms/HolomorphicMap.lean` — add `weightedFiberSum_constant_of_contMDiff` (the discrete deliverable above) just below `hasWeightedFiberConservation_of_contMDiff` (after line 1366).
- `Jacobians/Axioms/BranchLocus.lean` — replace `axiom AX_BranchLocus` (line 100) with `theorem AX_BranchLocus` proved by Steps 1–6; add the helper bridge lemma `localOrder_eq_mapAnalyticOrderAt_of_mem_fiber` (one-line `simp [localOrder, hxy]`) just above the new theorem, and `mapAnalyticOrderAt_gt_one_finite` (the Step-6 finiteness lemma, ~30 LOC implementing 6a–6e using `local_kfold_ramified_of_contMDiff` at `HolomorphicMap.lean:1082` + `IsCompact.elim_finite_subcover`).
- (no Mathlib PR; no new file.)

**Acceptance**
- `lake build Jacobians.Axioms.BranchLocus` succeeds with `axiom AX_BranchLocus` replaced by `theorem AX_BranchLocus` (no `sorry`).
- `#print axioms degreeImpl` (`Jacobians/Axioms/AbelJacobiMap.lean:566`) no longer lists `AX_BranchLocus`.
- `#print axioms AX_pushforward_pullback` (`Jacobians/Axioms/AbelJacobiMap.lean`, ROADMAP line 86) no longer lists `AX_BranchLocus` (its own derivation goes through, but `AX_pushforward_pullback` is still a separate axiom until that recipe runs).
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1 (from 90 to 89).

**Risk / escalation triggers**
- If the unramified-point cover construction in Step 6b somehow fails to yield `U_p ∩ R = ∅` (i.e., the `local_kfold_ramified_of_contMDiff` lemma at `HolomorphicMap.lean:1082` does not actually pin every point of `U_p` to order-1, only the points in `s`), fall back to the upper-semi-continuity route: prove `{p | mapAnalyticOrderAt f p ≥ 2}` is closed by translating `mapAnalyticOrderAt` through `chartLocalAt` into Mathlib's `analyticOrderNatAt` (`Mathlib/Analysis/Analytic/Order.lean:62`) and using `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero` (`Mathlib/Analysis/Analytic/IsolatedZeros.lean:125`) on each chart-local subtracted form. Do not escalate unless both routes fail.
- If `IsLocallyConstant.apply_eq_of_isPreconnected` (`Mathlib/Topology/LocallyConstant/Basic.lean:326`) or `LocallyConstant.eq_const` (line 334) is not in Mathlib v4.28 under that name (the API has shifted between `Topology.LocallyConstant.Basic` and `Topology.LocallyConstant.Algebra`), substitute the direct `IsClopen`-based proof of "locally constant on connected → constant"; do **not** escalate unless both routes fail.
- If the `ContMDiff … ω → ContMDiff … ⊤` coercion (`hf.of_le le_top`, used to feed `weightedFiberConservation_of_contMDiff`) does not typecheck because `ω` and `⊤` are not comparable in the project's pin of `WithTop ℕ∞`, escalate — this signals a Mathlib-API drift that affects far more than this recipe and should be fixed at the project-wide level, not patched locally. (Gemini's vetting also flagged this risk: if the axiom signature leaves `ω` completely unconstrained, the signature itself may need `(hω : ⊤ ≤ ω)`.)

**Gemini critique addressed:**
1. **Route confirmed `mathlib-now`.** The prior `[review]` caveat that re-classified this as `needs-infra` was based on a stale reading of the docstring: ROADMAP line 82's "manifold-level Open Mapping Theorem absent in Mathlib v4.28" is *actually* discharged inside the vendored Wallace module (`HolomorphicMap.lean:1199`) via Mathlib's `AnalyticOnNhd.is_constant_or_isOpenMap` (`Mathlib/Analysis/Complex/OpenMapping.lean:177`) applied chart-locally. The remaining work is pure glue between existing project decls and existing Mathlib decls — `IsLocallyConstant.apply_eq_of_isPreconnected` (`Mathlib/Topology/LocallyConstant/Basic.lean:326`), `tsum_eq_sum`, `IsCompact.elim_finite_subcover`, `Set.Finite.image` — all of which are in v4.28. The reclassification to `needs-infra` is withdrawn.
2. **Unramified-point coverage step added** (Step 6b above). The previous Step 6 attempted to extract a finite subcover of `R := {p | mapAnalyticOrderAt f p > 1}` directly from `CompactSpace X` by covering only the ramified locus — a fatal point-set topology error, since `CompactSpace X` only gives finite subcovers of open covers of all of `X`, not of subsets. The fix: construct an open neighborhood `U_p` *for every* `p ∈ X` (ramified or not) such that `U_p ∩ R ⊆ {p}`, then take the finite subcover of `X`. The unramified case (6b) is handled by `local_kfold_ramified_of_contMDiff` (`HolomorphicMap.lean:1082`) with `k = 1`, falling back to upper-semi-continuity of `analyticOrderNatAt` via `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero` (`Mathlib/Analysis/Analytic/IsolatedZeros.lean:125`) if needed.

---
**Vetting trail.** Critique: `_vetting/AX_BranchLocus.md`. Verdict: revise. Revised: 2026-06-03.

**Cross-plan patch (2026-06-03):** Standardised manifold-model-space notation to `𝓘(ℂ, ℂ)` (Mathlib's `modelWithCornersSelf ℂ ℂ`); the single-arg alias `𝓘(ℂ)` caused typeclass-unification failures between generic and concrete plans.
