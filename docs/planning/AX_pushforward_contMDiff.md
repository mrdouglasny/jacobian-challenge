> **✅ DISCHARGED — PR #88.** This axiom is now a proved theorem; this plan is retained as a historical record of the route, not active work. Canonical status: `AXIOM_AUDIT.md` → "Recently discharged".

# `AX_pushforward_contMDiff` — discharge recipe

**Location:** `Jacobians/Axioms/AbelJacobiMap.lean:582`
**Route:** needs-infra &nbsp;&nbsp; **Effort:** 5 &nbsp;&nbsp; **Est:** ~3–5 focused days, ~150–200 LOC (a substantial fraction shared with `AX_pullback_contMDiff`)
**Blocked by:** none

**Statement (verbatim):**
```lean
/-- **Axiom.** Pushforward on Jacobians is smooth. -/
axiom AX_pushforward_contMDiff {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] {Y : Type v} [TopologicalSpace Y] [T2Space Y]
    [CompactSpace Y] [ConnectedSpace Y] [Nonempty Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ, ℂ) ω Y] (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f) :
    ContMDiff (modelWithCornersSelf ℂ (Fin (genus X) → ℂ))
      (modelWithCornersSelf ℂ (Fin (genus Y) → ℂ)) ω (pushforwardImpl X Y f hf)
```

**Why it's an axiom right now:** The file's docstring (`Jacobians/Axioms/AbelJacobiMap.lean:17–20`) advertises `pushforwardImpl` as already being a real `def` constructed by `jacobianHomOfAmbient` (`AbelJacobiMap.lean:347–381`) out of the *continuous* ℂ-linear map `pushforwardAmbientLinear` (`AbelJacobiMap.lean:272–284`). The `Jacobian X →ₜ+ Jacobian Y` bundled hom already carries `continuous_toFun` (lines 373–381). Promoting "continuous" to "smooth" through the universe-lifted `ComplexTorus` quotient charts is mechanical — no genuinely new mathematics — provided the underlying `def` typechecks (which it does, as unproven axioms act as valid constants in the environment). The axiom is kept only because the smoothness proof through the four nested constructions (ULift / `ComplexTorus` quotient chart / linear map / dual / equivFun) requires tedious formal topological rigidity arguments, not because it's deep.

**Proof recipe**

The plan reduces "`pushforwardImpl` is `ContMDiff`" to "a ℂ-linear endomorphism of `Fin (genus X) → ℂ` is `ContMDiff` at the model level", composed with two charted-space transfer lemmas already in the project.

1. **Unfold `pushforwardImpl` to the `jacobianHomOfAmbient` form.** By the
   `def` at `Jacobians/Axioms/AbelJacobiMap.lean:542–549`,
   ```
   pushforwardImpl X Y f hf =
     jacobianHomOfAmbient X Y (pushforwardAmbientLinear f hf)
       (AX_pushforwardAmbient_preserves_lattice f hf)
   ```
   and `jacobianHomOfAmbient` (lines 347–381) packages a `Jacobian X →ₜ+ Jacobian Y` whose underlying function is
   ```
   p ↦ ULift.up (QuotientAddGroup.map LX LY L.toAddMonoidHom hL p.down)
   ```
   where `L = pushforwardAmbientLinear f hf`. Smoothness is a property of the underlying function, so it suffices to prove this composite is `ContMDiff` for the product model `modelWithCornersSelf ℂ (Fin (genus _) → ℂ)`.

2. **Strip the ULift wrappers.** Use `contMDiff_ulift_up` /
   `contMDiff_ulift_down` from `Jacobians/Jacobian/Construction.lean`
   (the ULift smoothness lemmas referenced in `AbelJacobiMap.lean:51–54`,
   defined in `Construction.lean:78–115`). Concretely, with
   `g : JacobianAmbient X → JacobianAmbient Y` defined by `q ↦ QuotientAddGroup.map LX LY L.toAddMonoidHom hL q`, the goal becomes `ContMDiff … g`. The Lie-group derivation at `AbelJacobiMap.lean:689–693` uses the same pattern (`infer_instance` after ULift transfer) as proof template.

3. **Reduce `QuotientAddGroup.map` to a `ComplexTorus`-level smoothness statement via topological rigidity.**
   `JacobianAmbient X = ComplexTorus (Fin (genus X) → ℂ) (periodLatticeInBasis …)`
   (`Construction.lean:132–136`). The charts on `ComplexTorus` are the
   `quotientBranch` local sections built in
   `Jacobians/AbelianVariety/ComplexTorus.lean:142–166`. To prove
   `ContMDiff` on a quotient by a discrete subgroup, it suffices to prove
   `ContMDiff` of one local lift, since `quotientBranch` is a smooth
   chart and `(extChartAt 𝓘(ℂ, V) p).symm z = QuotientAddGroup.mk' L.toAddSubgroup z`
   (`ComplexTorus.lean:166`).
   *The Rigidity Argument:* The local lift of `QuotientAddGroup.map LX LY L.toAddMonoidHom hL` through any pair of `quotientBranch` charts is mathematically `L : V → W` up to a constant lattice-translation. To formalize this, construct the difference map `x ↦ lift(map(x)) - L(x)`. Prove that this difference map is continuous and that its image lies entirely in the target lattice `LY`. Since `LY` is a discrete space and the source space is connected, invoke the topological theorem that a continuous map from a connected space to a discrete space is locally constant. This proves the difference is locally constant, and thus the local lift is just the linear map `L` plus a constant.

4. **A continuous ℂ-linear map on a finite-dim normed space is `ContMDiff` in the self-model.** Use `ContinuousLinearMap.contMDiff` (Mathlib `Mathlib.Geometry.Manifold.ContMDiffMFDeriv`), specialized to the self-model `modelWithCornersSelf ℂ (Fin (genus X) → ℂ)`. The continuity of `L = pushforwardAmbientLinear f hf` is exactly `L.continuous_of_finiteDimensional` (already cited inline at `AbelJacobiMap.lean:376–377` for `jacobianHomOfAmbient`'s `continuous_toFun` proof).

5. **Glue.** Assemble steps 2–4 into one helper `pushforwardImpl_contMDiff` (or use a shared helper since pullback is symmetric, see step 7). Write the helper in a new `Jacobians/Axioms/AbelJacobiMap/Smoothness.lean` to keep `AbelJacobiMap.lean` lean. Tactic sketch:
   ```
   theorem pushforwardImpl_contMDiff (f : X → Y) (hf : ContMDiff … f) :
       ContMDiff 𝓘(ℂ, Fin g_X → ℂ) 𝓘(ℂ, Fin g_Y → ℂ) ω (pushforwardImpl X Y f hf) := by
     unfold pushforwardImpl jacobianHomOfAmbient
     apply contMDiff_ulift_up.comp ((quotientMap_contMDiff_of_linear _).comp contMDiff_ulift_down)
   ```
   where `quotientMap_contMDiff_of_linear` is the new helper packaging step 3+4.

6. **Replace `axiom` with `theorem` at `Jacobians/Axioms/AbelJacobiMap.lean:582`** and import the helper.

7. **Share with `AX_pullback_contMDiff`.** The recipe for `AX_pullback_contMDiff` (`AbelJacobiMap.lean:631`) is symmetric — same `jacobianHomOfAmbient` skeleton with `pullbackAmbientLinear` in place of `pushforwardAmbientLinear`. Land the shared helper `jacobianHomOfAmbient_contMDiff` once; both axioms then collapse to one-line applications.

**Files touched**
- `Jacobians/Axioms/AbelJacobiMap.lean` — replace `axiom AX_pushforward_contMDiff` at line 582 with `theorem`; same line numbers for the structurally identical `AX_pullback_contMDiff` at line 631.
- `Jacobians/Axioms/AbelJacobiMap/Smoothness.lean` *(new, shared)* — defines `jacobianHomOfAmbient_contMDiff` (steps 2–5) consuming a `ContinuousLinearMap` argument; both `AX_pushforward_contMDiff` and `AX_pullback_contMDiff` cite it.

**Acceptance**
- `lake build Jacobians.Axioms.AbelJacobiMap` succeeds.
- `#print axioms Jacobians.Challenge.pushforward` (`Jacobians/Challenge.lean:150`, the immediate downstream consumer) no longer lists `AX_pushforward_contMDiff`.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1 (drops by 2 once `AX_pullback_contMDiff` lands alongside via the shared helper).

**Risk / escalation triggers**
- If the topological rigidity argument (Step 3) encounters issues because Mathlib lacks the specific API connecting connected-to-discrete continuous maps to local constancy, escalate to a human to avoid going down a deep topological rabbit hole.
- If the smoothness of `QuotientAddGroup.map` between `ComplexTorus` instances is not derivable from `quotientBranch` (`Jacobians/AbelianVariety/ComplexTorus.lean:142–166`) — e.g. because the `chartTarget` covering only yields smoothness on the chart source and a global gluing argument is required — escalate to a human, since this is a missing-Mathlib-API issue, not a textbook gap.
- If `ContinuousLinearMap.contMDiff` for the self-model is unavailable at the Mathlib pin and `LinearMap.continuous_of_finiteDimensional` (used at `AbelJacobiMap.lean:376–377`) does not lift to `ContMDiff` cleanly, escalate — the fix is a small Mathlib PR but blocks discharge.

## Gemini critique addressed
- **Route and Blockers:** Reclassified route to `needs-infra` and removed the `AX_pushforwardAmbient_preserves_lattice` blocker. Axioms act as valid constants in the environment, so Lean can reason about definitions like `pushforwardImpl` completely unblocked today.
- **Effort Recalibration:** Bumped Effort to 5 and the estimate to ~3-5 days to account for the tediousness of building generic manifold infrastructure for torus quotients.
- **Rigidity Gap Filled:** Explicitly revised Step 3 to include the topological rigidity argument (constructing the difference map, proving continuity, and leveraging the fact that continuous maps from connected spaces to discrete spaces are locally constant) to prove the local lift differs from the linear map by only a constant.

---
**Vetting trail.** Critique: `_vetting/AX_pushforward_contMDiff.md`. Verdict: revise. Revised: 2026-06-03.

**Cross-plan patch (2026-06-03):** Standardised manifold-model-space notation to `𝓘(ℂ, ℂ)` (Mathlib's `modelWithCornersSelf ℂ ℂ`); the single-arg alias `𝓘(ℂ)` caused typeclass-unification failures between generic and concrete plans.
