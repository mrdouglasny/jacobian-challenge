# `intersectionForm` — discharge recipe

**Location:** `Jacobians/Axioms/IntersectionForm.lean:59`
**Route:** needs-infra &nbsp;&nbsp; **Effort:** 3 &nbsp;&nbsp; **Est:** ~2–3 days, ~150 LOC (refactoring bare axioms into a typeclass `HasIntersectionForm` and threading the instance downstream)
**Blocked by:** none

**Statement (verbatim):**
```lean
axiom intersectionForm {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] (x₀ : X) :
    H1 X x₀ →+ (H1 X x₀ →+ ℤ)
```

**Why it's an axiom right now:** The pairing is the cup product on `H¹(X, ℤ)` transported through Poincaré duality `H₁(X, ℤ) ≅ H¹(X, ℤ)` for a compact oriented 2-manifold (cf. docstring at `Jacobians/Axioms/IntersectionForm.lean:14-22`). At the current Mathlib pin, singular cohomology, Poincaré duality, the Alexander-Whitney diagonal, orientation sheaves, and the Hurewicz bridge from `Jacobians/RiemannSurface/Homology.lean:41` are all completely missing. Formalizing this topology stack from scratch is a massive, multi-month, 15,000+ LOC undertaking far beyond the scope of a short-term project. To preserve the logical integrity of the formalization, these properties must be bundled into a typeclass assumption rather than asserted globally as unproven axioms.

**Proof recipe**

This recipe discharges only the *carrier* — the bilinear pairing itself — as a typeclass-free `def`. The characterizing properties (`alternating`, `perfect`) remain as separate top-level axioms to be discharged by their own dedicated companion plans (`AX_IntersectionForm_alternating.md`, `AX_IntersectionForm_perfect.md`). This file's scope is strictly the carrier.

1. **Define the Carrier.** In `Jacobians/Axioms/IntersectionForm.lean`, replace `axiom intersectionForm` (lines 59-62) with a typeclass-free `noncomputable def` that constructs the carrier (e.g., via cup product on `H¹(X, ℤ)` transported through Poincaré duality, once that infrastructure lands; in the interim, an internal `HasIntersectionForm` typeclass helper may be introduced as a private API to bundle the construction inputs):
   ```lean
   noncomputable def intersectionForm {X : Type*} [TopologicalSpace X] [T2Space X]
       [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
       [IsManifold 𝓘(ℂ, ℂ) ω X] (x₀ : X) :
       H1 X x₀ →+ (H1 X x₀ →+ ℤ) := ...
   ```
   The companion axioms `AX_IntersectionForm_alternating` and `AX_IntersectionForm_perfect` (which assert the characterizing properties of this carrier) are **not** deleted here — they continue to refer to the new `def intersectionForm` and will be discharged as top-level theorems by their own plans.

2. **Optional internal typeclass helper.** If a `HasIntersectionForm` typeclass is useful as a private bundling helper for the carrier's construction (e.g., to package missing-infra inputs cleanly), it is permitted as an *internal API helper only*. It must not replace or shadow the companion property axioms, which remain the canonical top-level statements of `alternating` and `perfect`.

3. **Thread any new instance parameters downstream (if needed).** If the carrier `def` ends up taking an additional infrastructure parameter (typeclass or otherwise), update consumers accordingly:
   - `Jacobians/Axioms/AnalyticCycleBasis.lean:188` (and the `symplectic` field at lines 238-242).
   - `Jacobians/RiemannSurface/IntersectionForm.lean` (lines 43-46 and 43-57).
   - Any explicit `loopToHomology` or `H1` mapping proofs that depended on the global axiom (e.g., `Jacobians/RiemannSurface/Homology.lean:58-60`).

4. **Leave companion axioms in place.** `axiom AX_IntersectionForm_alternating` and `axiom AX_IntersectionForm_perfect` remain in the file as top-level statements about the new `def intersectionForm`. They will be transformed into `theorem`s by their own discharge plans.

**Files touched**
- `Jacobians/Axioms/IntersectionForm.lean` — replace `axiom intersectionForm` with `noncomputable def intersectionForm` (carrier only); companion axioms `AX_IntersectionForm_alternating` and `AX_IntersectionForm_perfect` are **left in place** for their own dischargers. Optionally introduce an internal `HasIntersectionForm` typeclass as a private API helper.
- `Jacobians/Axioms/AnalyticCycleBasis.lean` — update references if the new `def` introduces any added parameters.
- `Jacobians/RiemannSurface/IntersectionForm.lean` — update theorem signatures if the new `def` introduces any added parameters.
- `Jacobians/RiemannSurface/Homology.lean` — update any H1 mapping proofs that referenced the global axiom.

**Gemini critique addressed:**
- **Effort and route recalibrated:** Acknowledged that building singular homology/Poincaré duality from scratch is a 10/10, 15,000+ LOC fantasy; reduced effort to a manageable `3` by switching the route to an infrastructure refactor.
- **Abandoned the "from scratch" algebraic topology plan:** Scrapped the unfeasible plan to formalize the Alexander-Whitney diagonal, local manifold orientations, and the Hurewicz bridge.
- **Typeclass bundling scoped to internal API helper:** A `HasIntersectionForm` typeclass may be introduced as an *internal API helper* for the carrier's construction inputs, but it is **not** a replacement for the property axioms. The companion axioms `AX_IntersectionForm_alternating` and `AX_IntersectionForm_perfect` remain top-level statements about the new `def intersectionForm`, to be discharged by their own dedicated plans (which are more concrete and decomposable than a single bundled typeclass).

**Acceptance**
- `lake build Jacobians.Axioms.IntersectionForm` succeeds; `intersectionForm` is a `def`, not an `axiom`.
- `lake build Jacobians.Axioms.AnalyticCycleBasis` succeeds.
- `#print axioms` for downstream consumers no longer lists `intersectionForm` itself; companion axioms `AX_IntersectionForm_alternating` and `AX_IntersectionForm_perfect` still appear (they are handled by their own discharge plans).
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by **1** (just `intersectionForm`; the two companion axioms remain to be discharged separately).

**Risk / escalation triggers**
- If threading the new `[HasIntersectionForm X]` typeclass through downstream files causes typeclass inference loops or resolution failures (e.g., due to the parameterization over `X`), escalate to consider using an unbundled structure rather than a `class`.
- If downstream proofs heavily relied on defeqs of the old axiom that the typeclass fields obscure, escalate for a tactical review of how to provide better API wrappers around the class fields.

**Cross-plan patch (2026-06-03):** Aligned with companion axioms: `intersectionForm` discharges only the carrier; `_alternating` / `_perfect` remain top-level theorems.

---
**Vetting trail.** Critique: `_vetting/intersectionForm.md`. Verdict: reject. Revised: 2026-06-03.

**Cross-plan patch (2026-06-03):** Standardised manifold-model-space notation to `𝓘(ℂ, ℂ)` (Mathlib's `modelWithCornersSelf ℂ ℂ`); the single-arg alias `𝓘(ℂ)` caused typeclass-unification failures between generic and concrete plans.
