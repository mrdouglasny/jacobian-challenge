# `AX_pullback_contMDiff` — discharge recipe

**Location:** `Jacobians/Axioms/AbelJacobiMap.lean:631`
**Route:** provable-from-other-axioms &nbsp;&nbsp; **Effort:** 1 &nbsp;&nbsp; **Est:** ~5 minutes, ~4 LOC once the shared helper from `AX_pushforward_contMDiff.md` lands
**Blocked by:** `AX_pullbackAmbient_preserves_lattice`

**Statement (verbatim):**
```lean
/-- **Axiom.** Pullback on Jacobians is smooth. -/
axiom AX_pullback_contMDiff {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] {Y : Type v} [TopologicalSpace Y] [T2Space Y]
    [CompactSpace Y] [ConnectedSpace Y] [Nonempty Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ, ℂ) ω Y] (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f) :
    ContMDiff (modelWithCornersSelf ℂ (Fin (genus Y) → ℂ))
      (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω (pullbackImpl X Y f hf)
```

**Why it's an axiom right now:** Exactly mirrors `AX_pushforward_contMDiff` (`Jacobians/Axioms/AbelJacobiMap.lean:582`): `pullbackImpl` (lines 552–559) is already a real `def` built by `jacobianHomOfAmbient` (lines 347–381) from the continuous ℂ-linear map `pullbackAmbientLinear` (lines 289–301). The bundled `Jacobian Y →ₜ+ Jacobian X` carries continuity (line 373); smoothness is a routine charted-space transfer through the `ComplexTorus` quotient charts. Kept as an axiom only because the manual smoothness boilerplate is verbose.

**Proof recipe**

Strictly symmetric to `AX_pushforward_contMDiff`; share the helper.

1. **Unfold `pullbackImpl` to the `jacobianHomOfAmbient` form.** By
   `Jacobians/Axioms/AbelJacobiMap.lean:552–559`:
   ```
   pullbackImpl X Y f hf =
     jacobianHomOfAmbient Y X (pullbackAmbientLinear f hf)
       (AX_pullbackAmbient_preserves_lattice f hf)
   ```
   Same `jacobianHomOfAmbient` constructor (lines 347–381) as in the pushforward case; only the direction `Y → X` and the underlying `L = pullbackAmbientLinear f hf` (lines 289–301) differ.

2. **Reuse the shared helper.** Cite `jacobianHomOfAmbient_contMDiff` (the new helper introduced in `AX_pushforward_contMDiff.md`, target file `Jacobians/Axioms/AbelJacobiMap/Smoothness.lean`). One application discharges the pullback case:
   ```
   theorem pullback_contMDiff (f : X → Y) (hf : ContMDiff … f) :
       ContMDiff 𝓘(ℂ, Fin g_Y → ℂ) 𝓘(ℂ, Fin g_X → ℂ) ω (pullbackImpl X Y f hf) := by
     unfold pullbackImpl
     exact jacobianHomOfAmbient_contMDiff
       (pullbackAmbientLinear f hf) (AX_pullbackAmbient_preserves_lattice f hf)
   ```
   The helper itself reduces to: (a) ULift transfer via `contMDiff_ulift_up` / `contMDiff_ulift_down` (`Jacobians/Jacobian/Construction.lean:78–115`, referenced inline at `AbelJacobiMap.lean:51–54`); (b) chart-local smoothness through `quotientBranch` (`Jacobians/AbelianVariety/ComplexTorus.lean:142–166`); (c) `ContinuousLinearMap.contMDiff` for the underlying ℂ-linear map (continuity supplied by `L.continuous_of_finiteDimensional` exactly as at `AbelJacobiMap.lean:376–377`). See `AX_pushforward_contMDiff.md` steps 2–5 for the full derivation; nothing changes other than the orientation `X ↔ Y`.

3. **Replace `axiom` with `theorem` at `Jacobians/Axioms/AbelJacobiMap.lean:631`.** Be sure the new name drops the `AX_` prefix to become exactly `pullback_contMDiff`.

**Files touched**
- `Jacobians/Axioms/AbelJacobiMap.lean` — replace `axiom AX_pullback_contMDiff` (line 631) with `theorem pullback_contMDiff`; one-line proof citing the shared helper.
- `Jacobians/Axioms/AbelJacobiMap/Smoothness.lean` — *no new code* if `AX_pushforward_contMDiff` has already landed; otherwise the shared helper must be added here (see `AX_pushforward_contMDiff.md`).

**Acceptance**
- `lake build Jacobians.Axioms.AbelJacobiMap` succeeds.
- `#print axioms Jacobians.Challenge.pullback` (`Jacobians/Challenge.lean:177`, the immediate downstream consumer) no longer lists `AX_pullback_contMDiff`.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1.

**Risk / escalation triggers**
- Any escalation trigger of `AX_pushforward_contMDiff.md` applies symmetrically — if the shared helper does not generalize cleanly to the `Y → X` direction (e.g. universe-variable ordering issues in `jacobianHomOfAmbient_contMDiff`'s signature), escalate to a human; the fix is parameter reordering, but it interacts with downstream `_id`/`_comp` lemmas.
- If `AX_pullbackAmbient_preserves_lattice` (`AbelJacobiMap.lean:324`) has not yet landed when this recipe is attempted, **stop** — `pullbackImpl` (line 552) does not typecheck without it (line 559 cites it directly).

**Gemini critique addressed:**
- Recalibrated Effort from 4 to 1 and the LOC/time estimate to "~5 minutes, ~4 LOC once the shared helper lands" to accurately reflect that this task is purely a trivial application of the new infrastructure.
- Corrected the replacement theorem name in Step 2 and Step 3 from `pullbackImpl_contMDiff` to `pullback_contMDiff` to adhere to standard `AX_` dropping conventions and ensure downstream continuity in `Jacobians/Challenge.lean:177`.

---
**Vetting trail.** Critique: `_vetting/AX_pullback_contMDiff.md`. Verdict: revise. Revised: 2026-06-03.

**Cross-plan patch (2026-06-03):** Standardised manifold-model-space notation to `𝓘(ℂ, ℂ)` (Mathlib's `modelWithCornersSelf ℂ ℂ`); the single-arg alias `𝓘(ℂ)` caused typeclass-unification failures between generic and concrete plans.
