# `AX_pathIntegral_local_antiderivative` — discharge recipe

**Location:** `Jacobians/Axioms/AbelJacobiMap.lean:116`
**Route:** needs-infra &nbsp;&nbsp; **Effort:** 9 &nbsp;&nbsp; **Est:** ~1 focused month, ~800 LOC (requires building Cauchy's theorem for convex chart balls, then closing the FTC sorry)
**Blocked by:** `pathIntegralBasepointFunctional`, `CauchyTheorem_local`

**Statement (verbatim):**
```lean
axiom AX_pathIntegral_local_antiderivative (X : Type*) [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (P₀ P : X) (form : HolomorphicOneForm X) :
    HasDerivAt
      (fun z : ℂ =>
        pathIntegralBasepointFunctional X P₀ ((extChartAt 𝓘(ℂ) P).symm z) form)
      (form.coeff P ((extChartAt 𝓘(ℂ) P) P))
      ((extChartAt 𝓘(ℂ) P) P)
```

**Why it's an axiom right now:** This is the Fundamental Theorem of Calculus for path integrals of holomorphic 1-forms, localised to a single chart at the upper endpoint. It binds `pathIntegralBasepointFunctional` to the cocycle-predicate content of `HolomorphicOneForm` (`Jacobians/RiemannSurface/OneForm.lean:118–142`), preventing the trivial-zero functional from silently satisfying downstream smoothness claims (`AX_ofCurve_contMDiff`) and injectivity (`AX_ofCurve_inj`). Per the docstring at lines 103–115, this axiom is paired with `pathIntegralBasepointFunctional` to make the pair load-bearing. The Lean realisation gap is the `sorry` in `Jacobians/Bridge/KirovLineIntegral.lean:357–364` (`kirovBackedFunctional_local_antiderivative`).

**Proof recipe (infrastructure + project-side derivation)**

Textbook reference: Forster Ch. I §10–13 (chart-local integration and Cauchy's theorem); Mumford Vol I §II.3; Griffiths-Harris Ch. 0.2. Forster is the primary citation for the analytic details required in Lean, specifically handling Cauchy's theorem to prove local exactness on convex chart balls.

Mathematical content:

1. **Setup.** A holomorphic 1-form on `X` is locally `coeff_p(z) dz` in the chart `φ_p` at `p` (`Jacobians/RiemannSurface/OneForm.lean:69–73` for the `IsHolomorphicOneFormCoeff` predicate).
2. **Local Path Independence (Cauchy's Theorem).** The integral from $P_0$ to a nearby $Q := \varphi_p^{-1}(z)$ cannot be trivially split without topological justification. We must establish Cauchy's theorem for convex chart balls: the line integral of a holomorphic 1-form is locally independent of the path.
3. **Chart-line FTC.** On the local piece between $P$ and $Q$, parameterize the straight line from `(φ_p P, z)` in chart space. Pull back via `φ_p.symm`, apply standard FTC for `intervalIntegral` (`intervalIntegral.integral_hasDerivAt_right`), and get derivative `coeff_p(φ_p P)` at `z = φ_p P`.
4. **Differentiation.** With path independence proven, the difference $\int_{P_0}^Q \omega - \int_{P_0}^P \omega$ evaluates exactly to the integral along the local straight chart-line, allowing us to compute the derivative via the chain rule.

Project-side discharge (Lean tactic plan):

1. **Discharge `pathIntegralBasepointFunctional` first** to a `def` per `pathIntegralBasepointFunctional.md` (redirect to `Jacobians.Bridge.kirovBackedFunctional`). This unblocks the FTC statement.

2. **Build missing infrastructure (`CauchyTheorem_local`).** Kirov's library needs local exactness/Cauchy's theorem for complex line integrals. Prove that for a holomorphic 1-form, the integral over any closed loop in a convex chart ball is zero, implying local path independence.

3. **Fill the `sorry` at `Jacobians/Bridge/KirovLineIntegral.lean:276–283` (`chartLine_FTC`).** Per the comment block at lines 243–259, this factors through six small lemmas:
   - `extChartAt_chartLine` (line 263) — already a theorem.
   - `pathSpeed_extChartAt_chartLine` — sketched but not present; add it (~30 LOC) using `derivWithin` of the affine line `(1-t)·a + t·z`.
   - `mfderiv_extChartAt_pathSpeed_chartLine` — combine the above with `Jacobians.Vendor.Kirov.pathSpeed_comp_eq_mfderiv` (cited in `Jacobians/Bridge/KirovLineIntegral.lean:104, 252`).
   - `bridgeForm_chartLine_integrand` — chart-swap to fixed chart at `P` via `rawCLM_swap_chart` (used in `Jacobians/Bridge/KirovHolomorphic.lean` ecosystem).
   - `lineIntegral_chartLine_eq` — change of variable `u = a + t(z - a)` reducing to `∫_a^z form.coeff P u du`.
   - `chartLine_FTC` — invoke `intervalIntegral.integral_hasDerivAt_right` + continuity of `form.coeff P` from `IsHolomorphicOneFormCoeff` at `Jacobians/RiemannSurface/OneForm.lean:69–73`.

4. **Fill the second `sorry` at `Jacobians/Bridge/KirovLineIntegral.lean:357–364` (`kirovBackedFunctional_local_antiderivative`).**
   - **Do NOT introduce a new property axiom** (completely scrapping earlier flawed plans).
   - Relying on the `CauchyTheorem_local` infrastructure, mathematically prove that for $Q$ in the convex chart ball of $P$, the line integral from $P_0$ to $Q$ evaluates to the integral from $P_0$ to $P$ plus the integral along the straight `chartLine P Q`. Local path independence justifies this split regardless of the global path chosen for $Q$.
   - Apply `HasDerivAt.const_add` (for the constant $P_0 \to P$ piece) plus `chartLine_FTC` for the moving-endpoint piece.

5. **Replace the axiom with a theorem.** In `Jacobians/Axioms/AbelJacobiMap.lean`, replace lines 116–123 with:
   ```lean
   theorem AX_pathIntegral_local_antiderivative (X : Type*) [TopologicalSpace X]
       [T2Space X] [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
       [IsManifold 𝓘(ℂ) ω X] (P₀ P : X) (form : HolomorphicOneForm X) :
       HasDerivAt
         (fun z : ℂ =>
           pathIntegralBasepointFunctional X P₀ ((extChartAt 𝓘(ℂ) P).symm z) form)
         (form.coeff P ((extChartAt 𝓘(ℂ) P) P))
         ((extChartAt 𝓘(ℂ) P) P) :=
     Jacobians.Bridge.kirovBackedFunctional_local_antiderivative P₀ P form
   ```

**Files touched**
- `Jacobians/Bridge/KirovLineIntegral.lean` — close the two `sorry`s at lines 276–283 and 357–364 using local exactness.
- `Jacobians/Axioms/AbelJacobiMap.lean` — replace `axiom AX_pathIntegral_local_antiderivative` (lines 116–123) with a `theorem` redirecting to `Jacobians.Bridge.kirovBackedFunctional_local_antiderivative`.

**Acceptance**
- `lake build Jacobians.Axioms.AbelJacobiMap` succeeds, with no new `sorry` in `Jacobians/Bridge/KirovLineIntegral.lean`.
- `#print axioms Jacobians.Axioms.ofCurveImpl` no longer lists `AX_pathIntegral_local_antiderivative`.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1.

**Risk / escalation triggers**
- If `Vendor.Kirov.pathSpeed_comp_eq_mfderiv` (and the surrounding chain-rule lemmas) do not match the chart pair `(ℝ, ℂ)` cleanly because of the real-vs-complex `ModelWithCorners` mismatch flagged at `Jacobians/Bridge/KirovLineIntegral.lean:175–185`, the proof shape needs revision — escalate before assuming a chart-local `C¹` substitute exists.
- Mumford §II.3 expresses the FTC abstractly via "the integral of an exact form along a path is the difference of antiderivatives at the endpoints"; the Lean statement uses the chart-local coefficient. Confirm the sign convention `form.coeff P (φ P)` (not `(φ P)`-shifted) matches the cocycle in `Jacobians/RiemannSurface/OneForm.lean:89–95` before committing the proof.

## Sub-plans needed
- `CauchyTheorem_local.md` — Major infrastructure: Cauchy's theorem / local exactness for holomorphic 1-forms on convex chart balls. This establishes the local path independence required to mathematically justify splitting path integrals.

**`Gemini critique addressed:`**
- Reclassified route to `needs-infra` and updated effort from 7 to 9 to account for heavy missing math infrastructure.
- Completely removed the illegal proposal to add the `bridgePath_chartLine_concat_eventually` axiom (Step 3a in the original).
- Inserted a required step to prove local path independence / Cauchy's theorem for convex chart balls, which mathematically justifies splitting the path integral without inventing axioms.
- Integrated Forster Ch. I §10-13 as the primary mathematical reference for chart-local integration and Cauchy's theorem.

---
**Vetting trail.** Critique: `_vetting/AX_pathIntegral_local_antiderivative.md`. Verdict: reject. Revised: 2026-06-03.