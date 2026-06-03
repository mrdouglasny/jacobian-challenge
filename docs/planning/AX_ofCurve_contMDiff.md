# `AX_ofCurve_contMDiff` — discharge recipe

**Location:** `Jacobians/Axioms/AbelJacobiMap.lean:238`
**Route:** provable-from-other-axioms &nbsp;&nbsp; **Effort:** 7 &nbsp;&nbsp; **Est:** ~1 focused week once `AX_pathIntegral_local_antiderivative` is a theorem, ~250–350 LOC
**Blocked by:** `AX_pathIntegral_local_antiderivative` (`Jacobians/Axioms/AbelJacobiMap.lean:116`); transitively `pathIntegralBasepointFunctional`.

**Statement (verbatim):**
```lean
axiom AX_ofCurve_contMDiff {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (P : X) :
    ContMDiff 𝓘(ℂ, ℂ) (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω
      (ofCurveImpl X P)
```

**Why it's an axiom right now:** `ofCurveImpl` (`Jacobians/Axioms/AbelJacobiMap.lean:229–233`) is a real `def` via `pathIntegralBasepointFunctional`, but smoothness is a *property* of that def. Without the FTC link (`AX_pathIntegral_local_antiderivative`, line 116), nothing forces the path-integral functional to be differentiable in the upper endpoint, so smoothness of `ofCurveImpl` cannot be derived. Per the docstring at lines 75–87, the FTC axiom is precisely the binding glue: with FTC, smoothness of `ofCurveImpl P` in `Q` (in a chart at `Q`) follows from each component being a holomorphic function of the chart parameter `z` (its derivative w.r.t. `z` is `coeff_i Q (φ_Q Q)`, which is itself holomorphic in `Q` because each `jacobianBasis X i : HolomorphicOneForm X` satisfies `IsHolomorphicOneFormCoeff` per `Jacobians/RiemannSurface/OneForm.lean:69–73`).

**Proof recipe**

Mathematical content (Mumford Vol I §II.3; Griffiths-Harris Ch. 2.3 p. 130): the Abel-Jacobi map `P ↦ (∫_{P_0}^P ω_i)_i` is holomorphic because each component has chart-local derivative equal to `coeff_i Q (φ_Q Q)` (FTC), and that coefficient is itself a holomorphic function of the chart parameter (`IsHolomorphicOneFormCoeff`).

Project-side discharge:

1. **Prerequisite: discharge `AX_pathIntegral_local_antiderivative`** to a theorem per `AX_pathIntegral_local_antiderivative.md`. This is the FTC; it is what binds the functional to differentiability data.

2. **Unfold `ofCurveImpl`.** `Jacobians/Axioms/AbelJacobiMap.lean:229–233` gives
   ```
   ofCurveImpl X P = fun Q => ULift.up (QuotientAddGroup.mk' L (ofCurveAmbient X P Q - ofCurveAmbient X P P))
   ```
   `ContMDiff` is preserved by `QuotientAddGroup.mk'` (it is a local diffeomorphism / covering map of Lie groups to the complex torus, so it is smooth via the Lie group quotient manifold lemmas, *not* via linearity tactics), `ULift.up` (use `Jacobians.Jacobian.Construction.contMDiff_ulift_up`, the lemma cited in `Jacobians/Axioms/AbelJacobiMap.lean:51–54`), and subtraction by a constant (the subtraction `ofCurveAmbient X P Q - ofCurveAmbient X P P` happens in the vector space `Fin (genus X) → ℂ` *before* the quotient map). So it suffices to show **`ofCurveAmbient X P : X → (Fin (genus X) → ℂ)` is `ContMDiff`**.

3. **Reduce to per-component smoothness.** Since the codomain is `Fin (genus X) → ℂ` with the product manifold structure, `ContMDiff` of a function into it is equivalent to `ContMDiff` of each component (Mathlib: `contMDiff_pi`). Each component is `fun Q => pathIntegralBasepointFunctional X P Q (jacobianBasis X i)`, i.e. the `i`-th basis form evaluated at the path integral.

4. **Per-component, work in the chart at the upper endpoint `Q`.** A function `Y → ℂ` is `ContMDiff 𝓘(ℂ) 𝓘(ℂ, ℂ) ω` iff its chart-pullback `z ↦ f((φ_Q).symm z)` is analytic in `z` for each `Q`. By `AX_pathIntegral_local_antiderivative` (`Jacobians/Axioms/AbelJacobiMap.lean:116–123`), that chart-pullback has derivative `(jacobianBasis X i).coeff Q (φ_Q Q)` at `z = φ_Q Q` — a `HasDerivAt` statement.

5. **Promote `HasDerivAt` at a single point to `AnalyticOn` on a chart-target neighbourhood.** This is the load-bearing step. Strategies:
   - **5a.** The `HasDerivAt` statement in the axiom (line 119–123) gives the derivative with respect to the *upper limit* `Q`. To get differentiability on the entire chart, we leave the basepoint `P` globally fixed and evaluate the FTC axiom at varying upper endpoints `Q'` inside the chart neighborhood. `IsHolomorphicOneFormCoeff` (`Jacobians/RiemannSurface/OneForm.lean:69–73`) provides analyticity of the `coeff` family on the whole chart target, so this procedure gives us a derivative `coeff ∘ φ` continuously on the chart target. We then use `Complex.analyticOn_of_differentiableOn` (Mathlib: `DifferentiableOn → AnalyticOn` on opens in ℂ via Morera/Goursat).
   - **5b.** Alternatively, use the Kirov-bridge realisation: if Route A of `pathIntegralBasepointFunctional.md` is taken (redirect to `Jacobians.Bridge.kirovBackedFunctional`), the functional unfolds to `Vendor.Kirov.lineIntegral ∘ bridgeForm`, and `Vendor.Kirov.lineIntegral`'s analyticity properties (look up in `Jacobians/Vendor/Kirov/LineIntegral.lean`) give the chart-pullback smoothness directly.

6. **Combine.** Per-component analyticity on the chart target gives `ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, ℂ) ω` per component. `contMDiff_pi` upgrades this to the product codomain. The constant subtraction + `QuotientAddGroup.mk'` + `ULift.up` finishes per step 2.

7. **Lean tactic sketch:**
   ```lean
   theorem AX_ofCurve_contMDiff {X : Type u} … (P : X) :
       ContMDiff 𝓘(ℂ, ℂ) (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω
         (ofCurveImpl X P) := by
     unfold ofCurveImpl
     apply (contMDiff_ulift_up).comp     -- Jacobian/Construction.lean
     -- Apply Lie group quotient smoothness (not linearity!)
     apply (contMDiff_quotient_mk).comp
     -- Subtraction happens in the vector space BEFORE the quotient
     apply ContMDiff.sub _ contMDiff_const  
     -- Reduce to ofCurveAmbient
     unfold ofCurveAmbient
     rw [contMDiff_pi_lambda]
     intro i
     -- per-component: chart-pullback analyticity from FTC + AnalyticOn from Morera
     intro Q
     -- Note: Need custom bridging lemma if Mathlib lacks exact analytic smoothness theorem
     rw [contMDiffAt_iff_analyticAt_extChart]   
     -- Basepoint P remains fixed; vary upper limit to build AnalyticOn
     have hFTC := AX_pathIntegral_local_antiderivative X P Q (jacobianBasis X i)
     exact Complex.analyticOn_of_differentiableOn … |>.contMDiffAt
   ```

8. **Replace `axiom` with `theorem`** at `Jacobians/Axioms/AbelJacobiMap.lean:238–242`. Signature unchanged.

### Gemini critique addressed:
*   **Recalibrated effort:** Increased Effort from 5 to 7 and estimate to ~250-350 LOC, acknowledging the painful chart-domain bookkeeping needed to move from `HasDerivAt` to `ContMDiff ... ω` (analytic smoothness).
*   **Corrected Lie group quotient logic:** Removed the mathematically false claim that `QuotientAddGroup.mk'` into a complex torus is "linear" and "automatically smooth." Clarified that it relies on Lie group covering / quotient manifold lemmas.
*   **Corrected FTC Basepoint mechanics:** Removed the nonsense about "translating the fixed basepoint P." Fixed the recipe to clearly state that differentiability on the chart is achieved by keeping `P` fixed while varying the *upper limit* `Q'` inside the chart neighborhood.
*   **Clarified Tactic Sketch subtraction:** Explicitly documented that the `ofCurveAmbient X P Q - ofCurveAmbient X P P` vector space subtraction occurs *before* the quotient map application.

**Files touched**
- `Jacobians/Axioms/AbelJacobiMap.lean` — replace `axiom AX_ofCurve_contMDiff` (lines 238–242) with a `theorem` using `AX_pathIntegral_local_antiderivative` (the theorem version per step 1) + `IsHolomorphicOneFormCoeff` (`Jacobians/RiemannSurface/OneForm.lean:69–73`) + `Complex.analyticOn_of_differentiableOn` (Mathlib).
- (Possibly) `Jacobians/Jacobian/Construction.lean` — if `contMDiff_quotient_mk` / `contMDiff_ulift_up` need a small wrapper not currently in the file. (The cited lemmas `contMDiff_ulift_up` / `contMDiff_ulift_down` exist per the docstring at `Jacobians/Axioms/AbelJacobiMap.lean:51–54`.)

**Acceptance**
- `lake build Jacobians.Axioms.AbelJacobiMap` succeeds.
- `#print axioms Jacobians.Axioms.AX_ofCurve_contMDiff` (now a theorem) does not list itself.
- Downstream: any use of `AX_ofCurve_contMDiff` (search the repo with `grep -rn "AX_ofCurve_contMDiff" --include="*.lean"`) continues to work transparently.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1.

**Risk / escalation triggers**
- The `HasDerivAt`-at-a-single-point → `AnalyticOn`-on-chart-target step (5a/5b) is the chief hidden complication. If Mathlib at this pin lacks a one-step `Complex.analyticOn_of_differentiableOn`, the project may need a vendored Morera-style helper — escalate before adding a new global axiom.
- The chart-pullback equivalence (step 7) for `ContMDiffAt` on a charted space with `𝓘(ℂ)` model is delicate; if the project's existing examples (e.g., `Jacobians.Vendor.Kirov.pullbackForm` at `Jacobians/Vendor/Kirov/HolomorphicForms.lean:122–202`) use a non-trivial alternative pattern (`contMDiffAt_hom_bundle` at line 130), follow that pattern rather than inventing a new one. Be prepared to write a custom bridging lemma if Mathlib lacks the exact `contMDiffAt_iff_analyticAt_extChart` theorem for index `ω`.
- If `AX_pathIntegral_local_antiderivative` is *not* yet discharged (still an axiom), this proof can still be written using the axiom form (does *not* reduce axiom count yet, but cleans the dependency graph). Note: in that intermediate state, axiom-count remains unchanged because we replace one axiom with another's hypothesis.

---
**Vetting trail.** Critique: `_vetting/AX_ofCurve_contMDiff.md`. Verdict: revise. Revised: 2026-06-03.