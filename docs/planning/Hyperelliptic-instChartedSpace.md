# `Hyperelliptic.instChartedSpace` — discharge recipe

**Location:** `Jacobians/ProjectiveCurve/Hyperelliptic.lean:81`
**Route:** needs-infra &nbsp;&nbsp; **Effort:** 3 &nbsp;&nbsp; **Est:** ~4 focused days, ~150 LOC — handling the parity-dispatch assembly and base charts. Assumes the 7 heavy sub-axioms in `OddAtlas/InfinityChart.lean` are completed under their own recipes.
**Blocked by:** `Hyperelliptic`, `AX_Hyperelliptic_oddEquiv`, `AX_Hyperelliptic_evenEquiv`, plus the atlas axioms listed below.

**Statement (verbatim):**
```lean
axiom Hyperelliptic.instChartedSpace (H : HyperellipticData) :
    ChartedSpace ℂ (Hyperelliptic H)
attribute [instance] Hyperelliptic.instChartedSpace
```

**Why it's an axiom right now:** The atlas plan in `docs/hyperelliptic-atlas-plan.md` §H4 is only partially executed. The even-parity atlas already exists as a real `noncomputable instance instChartedSpace` on `HyperellipticEvenProj H` (`Hyperelliptic/EvenAtlas.lean:173-180`), but the odd-parity atlas relies on the chart at infinity (`HyperellipticOdd.infinityChart`) which is still an axiom (`Hyperelliptic/OddAtlas/InfinityChart.lean:58-59`) and has not yet been assembled into a `ChartedSpace ℂ (HyperellipticOdd H h)`. The unified `Hyperelliptic` axiom defers the parity-dispatch lift until both halves are real.

**Proof recipe**

This is a *bounded infrastructure* axiom. The infrastructure consists of three blocks; once they land the lift through the parity equivalences is mechanical.

1. **Block A — odd-parity atlas (the missing half).** Build a real `instance : ChartedSpace ℂ (HyperellipticOdd H h)`. The pieces:
   - The affine chart-family `HyperellipticAffine.affineChartAt` is already real (used by the even side at `Hyperelliptic/EvenAtlas.lean:117-119`). Lift it to a chart on `HyperellipticOdd H h = OnePoint (HyperellipticAffine H)` (`Hyperelliptic/Basic.lean:136-137`) using `OnePoint.isOpenEmbedding_coe`. Create the partial homeomorphism on the superspace via `(OpenEmbedding.toPartialHomeomorph OnePoint.isOpenEmbedding_coe).symm.trans (HyperellipticAffine.affineChartAt ...)`. This mirrors the pattern at `EvenAtlas.lean:113-128`.
   - At the point `∞ : OnePoint (HyperellipticAffine H)`, use `HyperellipticOdd.infinityChart H h` (`OddAtlas/InfinityChart.lean:58-59` — handled by its own recipe `infinityChart.md` via `infinityInverseMap.md`).
   - Membership at the basepoint is `infinityChart_mem_source` (`OddAtlas/InfinityChart.lean:62-63`; recipe: `infinityChart_mem_source.md`).
   - Define `chartAt : HyperellipticOdd H h → PartialHomeomorph (HyperellipticOdd H h) ℂ` by `OnePoint.rec`: send `↑p` to the lifted affine chart at `p`, and `∞` to `infinityChart H h`. Mirror the `mem_chartAt_source` proof in `EvenAtlas.lean:148-171`.
   - Package as `instance : ChartedSpace ℂ (HyperellipticOdd H h)` — direct port of the `EvenAtlas.lean:174-180` shape.
2. **Block B — even-parity atlas (already real).** `Hyperelliptic.lean:36-44` already declares `HyperellipticEven H h := HyperellipticEvenProj H`, and `EvenAtlas.lean:174-180` provides `instChartedSpace ℂ (HyperellipticEvenProj H)` under `Fact (¬ Odd H.f.natDegree)`. Wrap with `haveI : Fact ... := ⟨h⟩` to expose the instance through the abbreviation.
3. **Block C — parity-dispatched lift.** Mathlib `ChartedSpace` is data-carrying; DO NOT use a top-level `by_cases` or the charts will fail to reduce. Instead, push the case split into the structure fields and use `PartialHomeomorph.trans` to pull back the charts along the equivalence:
   ```lean
   noncomputable instance Hyperelliptic.instChartedSpace (H : HyperellipticData) :
       ChartedSpace ℂ (Hyperelliptic H) where
     atlas := if h : Odd H.f.natDegree
              then Set.image (fun c => (AX_Hyperelliptic_oddEquiv H h).toPartialHomeomorph.trans c) (ChartedSpace.atlas ℂ (HyperellipticOdd H h))
              else Set.image (fun c => (AX_Hyperelliptic_evenEquiv H h).toPartialHomeomorph.trans c) (ChartedSpace.atlas ℂ (HyperellipticEven H h))
     chartAt p := if h : Odd H.f.natDegree
                  then (AX_Hyperelliptic_oddEquiv H h).toPartialHomeomorph.trans (chartAt ℂ ((AX_Hyperelliptic_oddEquiv H h) p))
                  else (AX_Hyperelliptic_evenEquiv H h).toPartialHomeomorph.trans (chartAt ℂ ((AX_Hyperelliptic_evenEquiv H h) p))
     mem_chartAt_source p := by
       split_ifs with h
       -- prove using mem_source of trans and mem_chartAt_source of the respective spaces
       sorry
       sorry
     chart_mem_atlas p := by
       split_ifs with h
       -- exact Set.mem_image_of_mem _ (chart_mem_atlas _)
       sorry
       sorry
   ```
4. Once landed, also retire `Hyperelliptic.instT2Space` / `instCompactSpace` / `instConnectedSpace` / `instNonempty` (separate recipes; each effort 1) since the parity-dispatch instance machinery is now in place.
5. Replace `axiom Hyperelliptic.instChartedSpace` with the `noncomputable instance ...` in `Jacobians/ProjectiveCurve/Hyperelliptic.lean` (drop line 83 `attribute [instance]`).

**Sub-axioms to discharge first** (handled in separate recipes):
- `infinityInverseMap`, `infinityChart`, `infinityChart_mem_source`, `infinityChart_compat_affineLiftProjX`, `affineLiftProjX_compat_infinityChart`, `infinityChart_compat_affineLiftProjY`, `affineLiftProjY_compat_infinityChart` — all in `Hyperelliptic/OddAtlas/InfinityChart.lean:48-111` (7 axioms; see `OddAtlas/InfinityChart.lean.md`-family of recipes and `docs/hyperelliptic-odd-atlas-plan.md`).
- `affineLiftChart_compat_infinityLiftChart`, `infinityLiftChart_compat_affineLiftChart` — `Hyperelliptic/EvenAtlas.lean:243-257` (cross-summand transitions, needed only by `instIsManifold`, not `instChartedSpace`, but their absence prevents downstream consumers from using the manifold structure).
- `squareLocalHomeomorph_zero_notMem_source`, `polynomialLocalHomeomorph_no_critical_in_source` — `Hyperelliptic/AffineForm.lean:66, 247` (IFT chart-source axioms; only blocking analyticity proofs, not the ChartedSpace data).

**Files touched**
- `Jacobians/ProjectiveCurve/Hyperelliptic/OddAtlas.lean` — assemble `chartAt` and `instance : ChartedSpace ℂ (HyperellipticOdd H h)`.
- `Jacobians/ProjectiveCurve/Hyperelliptic.lean` — replace `axiom Hyperelliptic.instChartedSpace` (lines 81–83) with a `noncomputable instance` doing parity dispatch through `AX_Hyperelliptic_oddEquiv` / `AX_Hyperelliptic_evenEquiv`.
- `docs/hyperelliptic-atlas-plan.md` — update Phase H4 status.

**Acceptance**
- `lake build Jacobians.ProjectiveCurve.Hyperelliptic` succeeds.
- `#print axioms genus_Hyperelliptic_eq` (`Hyperelliptic.lean:109`) no longer lists `Hyperelliptic.instChartedSpace`.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1 (and unblocks `Hyperelliptic.instIsManifold` and `AX_Hyperelliptic_genus`).

**Risk / escalation triggers**
- If the explicit case split inside the `ChartedSpace` constructor fields results in unmanageable proofs of `mem_chartAt_source` due to typeclass loop timeouts, the unified `Hyperelliptic H` may need to be a `def` first (recipe `Hyperelliptic.md`) so the dispatch happens inherently rather than by equivalence — escalate to revise the encoding choice.
- If discharging `infinityChart` via its sub-recipes stalls on analytic continuation around the branch at ∞, the odd-side atlas is blocked; escalate by ensuring the seven `OddAtlas/InfinityChart` axioms remain unblocked upstream.

**Gemini critique addressed:**
- **API hallucination (`OpenPartialHomeomorph`):** Replaced with `PartialHomeomorph` throughout.
- **API hallucination (`lift_openEmbedding`):** Replaced invalid operation with the correct Mathlib construct: `(OpenEmbedding.toPartialHomeomorph i).symm.trans chart`.
- **API hallucination & Typeclass Antipattern (`ChartedSpace.comp`):** Replaced top-level `by_cases` with a manual definition that pushes the `if h : ...` case splits into the data fields of the `ChartedSpace` constructor, avoiding definitionally stuck records.
- **Effort recalibration:** Reduced Effort from 7 to 3. The 7 heavy `InfinityChart` axioms are correctly delegated to their respective discharge recipes; this PR is scoped solely to the topological base charts and parity assembly.

---
**Vetting trail.** Critique: `_vetting/Hyperelliptic-instChartedSpace.md`. Verdict: revise. Revised: 2026-06-03.