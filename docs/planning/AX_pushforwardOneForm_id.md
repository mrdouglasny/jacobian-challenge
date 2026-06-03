# `AX_pushforwardOneForm_id` — discharge recipe

**Location:** `Jacobians/Axioms/AbelJacobiMap.lean:190`
**Route:** needs-infra &nbsp;&nbsp; **Effort:** 3 &nbsp;&nbsp; **Est:** ~1 focused day post-infra, ~30–60 LOC
**Blocked by:** `pushforwardOneForm` (this is a *characterising* property of that `def`; cannot become a theorem until the underlying `def` and its trace map API exist).

**Statement (verbatim):**
```lean
axiom AX_pushforwardOneForm_id {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] :
    pushforwardOneForm (id : X → X) contMDiff_id = LinearMap.id
```

**Why it's an axiom right now:** `pushforwardOneForm` is itself an axiom (`Jacobians/Axioms/AbelJacobiMap.lean:146–151`) with no underlying construction, so identities about it cannot be derived — they must be assumed. Mirrors the structure of the dual pair `AX_pullbackOneForm_id` (`Jacobians/Axioms/AbelJacobiMap.lean:162–169`), which *is* a theorem because `pullbackOneForm` is a real `def` (line 130–138) and the proof reduces to `Jacobians.Vendor.Kirov.pullbackForm_id` (`Jacobians/Vendor/Kirov/HolomorphicForms.lean:205–212`). The roadmap (`docs/planning/ROADMAP.md:57`) prescribes "fiber over identity has one point, multiplicity 1" — i.e., once `pushforwardOneForm` is constructed fiberwise (per `pushforwardOneForm.md`), the identity case has `f⁻¹(q) = {q}` with `localOrder id q q = 1`, so the trace sum has one term equal to the identity pullback.

**Proof recipe**

This is `needs-infra`. The theorem is heavily blocked by a major infrastructure project: constructing the trace map for differentials over a Riemann surface.

1. **The Infrastructure Piece.** Constructing the trace map over a Riemann surface—handling the sum over preimages, local branches, and analytic continuation over the branch locus. Standard literature for the definition of the trace of a differential on a Riemann surface: Forster's *Lectures on Riemann Surfaces*, Section 17, or Miranda's *Algebraic Curves and Riemann Surfaces*, Chapter VI.

2. **Discharge `pushforwardOneForm` first.** Per `pushforwardOneForm.md`, replace `axiom pushforwardOneForm` at `Jacobians/Axioms/AbelJacobiMap.lean:146–151` with a `noncomputable def` based on the fiberwise trace formula.

3. **Compute the identity fiber (post-infra discharge).** For `f = id : X → X` and any `q : X`, `f⁻¹(q) = {q}` is a single point. From `localOrder_pow {k := 1}` (`Jacobians/Axioms/BranchLocus.lean:86–94`) with `k = 1`, `localOrder (id : X → X) q q = 1` since `id` is locally `z ↦ z` in any chart. The fiber sum from the unramified branch of the trace definition reduces to one term:
   ```
   (pushforwardOneForm id _) ω at q  =  ω.coeff q (φ_q⁻¹(w)) · (id_chart)' w
                                     =  ω.coeff q (φ_q(q)) · 1
                                     =  ω.coeff q w
   ```
   where the last step uses that the chart-local representative of `id` is also `id` and `deriv id = 1`. Hence `(pushforwardOneForm id _) ω = ω` for all `ω`.

4. **Write the Lean proof** (template, exactly mirroring the pullback proof at `Jacobians/Axioms/AbelJacobiMap.lean:162–169`):
   ```lean
   theorem AX_pushforwardOneForm_id {X : Type u} [TopologicalSpace X] [T2Space X]
       [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
       [IsManifold 𝓘(ℂ) ω X] :
       pushforwardOneForm (id : X → X) contMDiff_id = LinearMap.id := by
     unfold pushforwardOneForm  -- after step 2, this unfolds to the trace def
     ext form
     apply HolomorphicOneForm.ext_of_coeff  -- Jacobians/RiemannSurface/OneForm.lean:182–184
     ext q w
     -- show (Σ' p, …) reduces to form.coeff q w
     simp only [Finset.sum_singleton_eq_at_id, localOrder_pow]
     -- finish with mfderiv_id (Mathlib) + deriv_id (Mathlib)
     simp [mfderiv_id]
   ```
   The exact lemma names will depend on how `pushforwardOneForm` is constructed in step 2. The key Mathlib lemmas are `mfderiv_id` (used analogously at `Jacobians/Vendor/Kirov/HolomorphicForms.lean:210–212`) and `Finset.sum_singleton` / `tsum_eq_single`.

5. **Replace `axiom` with `theorem`** at `Jacobians/Axioms/AbelJacobiMap.lean:190–193`. Signature unchanged.

**Files touched**
- `Jacobians/Axioms/AbelJacobiMap.lean` — replace `axiom AX_pushforwardOneForm_id` (lines 190–193) with a `theorem` whose proof unfolds the trace definition of `pushforwardOneForm` and uses `localOrder_pow` (`Jacobians/Axioms/BranchLocus.lean:86`) + `mfderiv_id` (Mathlib). The downstream lemma `pullbackAmbientLinear_id` at lines 490–495 already cites this — it will automatically use the theorem version.

**Acceptance**
- `lake build Jacobians.Axioms.AbelJacobiMap` succeeds.
- `#print axioms Jacobians.Axioms.pullbackAmbientLinear_id` (which uses this — see `Jacobians/Axioms/AbelJacobiMap.lean:490–495`) no longer lists `AX_pushforwardOneForm_id`.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1.

**Risk / escalation triggers**
- If `pushforwardOneForm` is built with a tsum (not a Finset.sum) the simp lemma `Finset.sum_singleton` does not directly apply — escalate to determine the right `tsum_eq_single` / `tsum_eq_zero_of_not_summable` invocation.

### Gemini critique addressed:
- **Route updated:** Changed from `provable-from-other-axioms` to `needs-infra` to properly reflect the dependency on the massive missing trace map infrastructure.
- **Removed invalid proof alternative:** Completely purged the dualized proof route (Step 4), which incorrectly confused the linear dual of the pullback with the trace map of differentials.
- **Added citations:** Included standard textbook citations (Forster Sec. 17 / Miranda Ch. VI) for the definition of the trace of a differential on a Riemann surface to ground the infrastructure step.

---
**Vetting trail.** Critique: `_vetting/AX_pushforwardOneForm_id.md`. Verdict: revise. Revised: 2026-06-03.