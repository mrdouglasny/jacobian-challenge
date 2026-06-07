# `AX_pullbackAmbient_preserves_lattice` — discharge recipe

**Location:** `Jacobians/Axioms/AbelJacobiMap.lean:324`
**Route:** needs-infra &nbsp;&nbsp; **Effort:** 9 &nbsp;&nbsp; **Est:** ~4–6 weeks, ~800–1200 LOC (requires heavy homology transfer infrastructure)
**Blocked by:** `AX_AnalyticCycleBasis`, `AX_PeriodLattice`, `AX_BranchLocus`

**Statement (verbatim):**
```lean
/-- **Axiom.** Lattice preservation for pullback. Symmetric to
`AX_pushforwardAmbient_preserves_lattice`. -/
axiom AX_pullbackAmbient_preserves_lattice {X : Type u}
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [ConnectedSpace Y] [Nonempty Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ, ℂ) ω Y] (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f) :
    ∀ v ∈ (periodLatticeInBasis Y (Classical.arbitrary Y)
              (jacobianBasis Y)).toAddSubgroup,
      (pullbackAmbientLinear f hf) v ∈
        (periodLatticeInBasis X (Classical.arbitrary X)
          (jacobianBasis X)).toAddSubgroup
```

**Why it's an axiom right now:** Mirror of `AX_pushforwardAmbient_preserves_lattice`. `pullbackAmbientLinear` (`Jacobians/Axioms/AbelJacobiMap.lean:289–301`) is built dually using `pushforwardOneForm` (`Jacobians/Axioms/AbelJacobiMap.lean:146`, still axiomatic). The mathematics is period-map naturality: pulling a 1-form back along `f` is dual to pushing a 1-cycle forward along `f`. Mumford Vol I §III; Griffiths–Harris Ch. 2.6 *Topology of Algebraic Varieties* — for finite covers the change-of-variable for trace integrals.

**Proof recipe**

1. **Case Split on Map Constancy.** First, split the proof on whether `f` is constant.
   - If `f` is constant, its derivative is zero, so the induced `pushforwardOneForm` (`Jacobians/Axioms/AbelJacobiMap.lean:146`) evaluates to 0. Consequently, `pullbackAmbientLinear f hf` is the zero map. Since `periodLatticeInBasis` is an `AddSubgroup`, it contains `0`, and the statement holds trivially.
   - If `f` is non-constant, because `X` and `Y` are compact connected Riemann surfaces, `f` must be a finite branched cover. Proceed to step 2.

2. **Homology Transfer Infrastructure (`needs-infra`).** For the non-constant case, construct the transfer/trace map `pullbackH1 : H1 Y →ₗ[ℤ] H1 X`.
   - Cite `AX_BranchLocus` (`Jacobians/Axioms/BranchLocus.lean:100–109`) to obtain a finite branch locus and common degree `d`.
   - Define the standard algebraic-topology *transfer* map for finite covers (Hatcher §3.G): for a small loop in `Y` avoiding the branch locus, lift to the disjoint union of `d` loops in `X` and extend ℤ-linearly.

3. **Introduce Trace Identity Helper Axiom.** Because `pushforwardOneForm` (`Jacobians/Axioms/AbelJacobiMap.lean:146`) is currently an opaque axiom, we cannot intrinsically prove its integral evaluation properties. Create a new intermediate axiom, `AX_pushforwardOneForm_integral_trace`, explicitly postulating the integral trace duality:
   $\int_{f^* \gamma} \omega = \int_\gamma f_* \omega$
   (i.e., integrating `ω` over the transfer `pullbackH1 γ` equals integrating `pushforwardOneForm ω` over `γ`).

4. **Pullback period-map naturality.** State and prove (in the `Jacobians/Axioms/PeriodLattice.lean` file):
   ```lean
   theorem periodMap_pullback_naturality
       (f : X → Y) (hf : ContMDiff … f)
       (γ : H1 Y x₀_Y) (ω : HolomorphicOneForm X) :
     (periodMapInBasis X x₀ b_X) (pullbackH1 f hf γ) =
       (pullbackAmbientLinear f hf) ((periodMapInBasis Y x₀_Y b_Y) γ)
   ```
   Discharge: Unfold `pullbackAmbientLinear` (lines 289–301) and reduce both sides to the evaluation of forms on cycles. Apply the newly introduced `AX_pushforwardOneForm_integral_trace` to establish the equality.

5. **Conclude lattice preservation.** Use `periodLatticeInBasis Y x₀_Y b_Y = LinearMap.range (periodMapInBasis Y x₀_Y b_Y)` (`PeriodLattice.lean:63–68`).
   - For `v` in this range, write `v = periodMapInBasis Y x₀_Y b_Y γ`.
   - By step 4, `pullbackAmbientLinear f hf v = periodMapInBasis X x₀ b_X (pullbackH1 f hf γ)`.
   - This explicitly lands in `LinearMap.range (periodMapInBasis X x₀ b_X) = periodLatticeInBasis X x₀ b_X`. Use `Submodule.mem_range`.

6. **Handle the `Classical.arbitrary` basepoint mismatch.** Use `periodLatticeInBasis_basepoint_independent` (from the pushforward naturality recipe) to normalize basepoints.

7. **Replace `axiom` with `theorem` at `Jacobians/Axioms/AbelJacobiMap.lean:324`.**

**Files touched**
- `Jacobians/Axioms/AbelJacobiMap.lean` — replace `axiom AX_pullbackAmbient_preserves_lattice` (line 324) with `theorem`; add the constant map case split; cite `periodMap_pullback_naturality` and discharge.
- `Jacobians/Axioms/PeriodLattice.lean` — adds `periodMap_pullback_naturality` using the homology transfer map and integral trace helper axiom.
- `Jacobians/Axioms/H1Functoriality.lean` — builds out the `pullbackH1` (homological transfer) infrastructure.
- `Jacobians/Axioms/PushforwardTrace.lean` (new) — introduces the helper trace integration axiom `AX_pushforwardOneForm_integral_trace`.

**Acceptance**
- `lake build Jacobians.Axioms.AbelJacobiMap` succeeds.
- `#print axioms Jacobians.Axioms.pullbackImpl` (`Jacobians/Axioms/AbelJacobiMap.lean:552`, the immediate consumer at line 559) no longer lists `AX_pullbackAmbient_preserves_lattice` (though it will list the new `AX_pushforwardOneForm_integral_trace`).
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; net axiom count remains equivalent (swapping lattice axiom for the trace integral axiom) until the infra is fully landed.

**Risk / escalation triggers**
- The homological transfer map `pullbackH1` requires delicate multivalued analytic continuation and dealing with singular homology of branched covers. This is a very heavy infrastructure step.
- Escalation is necessary if building the constant map case split fails due to missing Mathlib API for identifying smooth derivatives of constant maps to 0 in this specific manifold vector bundle setting.

## Sub-plans needed
- `AX_pushforwardOneForm_integral_trace.md` — A new helper axiom linking the homology transfer map `pullbackH1` with the existing opaque `pushforwardOneForm` axiom via integration duality ($\int_{f^* \gamma} \omega = \int_\gamma f_* \omega$).

## Gemini critique addressed
- **Route & Effort Recalibration:** Changed route to `needs-infra` and increased effort to `9`, extending the estimate to 4-6 weeks to reflect the massive formalization undertaking of building the singular homology transfer map for finite branched covers.
- **Fatal Circularity Avoided:** Completely removed the "pragmatic alternative" definition of `pullbackH1`, which invalidly assumed the period map's inverse would automatically yield an integral class before the theorem itself was proven.
- **Missing Constant Map Case:** Added a specific case split in Step 1 to explicitly handle constant maps, for which the pushforward of forms (and thus pullback of periods) is trivially zero, meaning lattice membership is trivially satisfied.
- **Trace Identity Helper:** Addressed the trace hallucination by officially splitting out `AX_pushforwardOneForm_integral_trace`. Since `pushforwardOneForm` is an opaque axiom, this new axiom is strictly required to provide the integration duality linking it to the homology transfer.

---
**Vetting trail.** Critique: `_vetting/AX_pullbackAmbient_preserves_lattice.md`. Verdict: reject. Revised: 2026-06-03.

**Cross-plan patch (2026-06-03):** Standardised manifold-model-space notation to `𝓘(ℂ, ℂ)` (Mathlib's `modelWithCornersSelf ℂ ℂ`); the single-arg alias `𝓘(ℂ)` caused typeclass-unification failures between generic and concrete plans.
