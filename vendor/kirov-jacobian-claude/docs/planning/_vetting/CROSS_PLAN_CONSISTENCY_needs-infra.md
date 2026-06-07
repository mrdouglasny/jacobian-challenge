# Cross-plan consistency audit — 33 `needs-infra` plans

**Model:** gemini-3.1-pro-preview  (extended thinking)
**Duration:** 117.0s
**Plans audited:** 33
**Date:** 2026-06-03

---

## Finding 1 — Typeclass bundling invalidates companion proofs
**Plans involved:** `intersectionForm`, `AX_IntersectionForm_alternating`, `AX_IntersectionForm_perfect`
**Class:** stale
**Evidence:**
Plan `intersectionForm` plans to delete the companion axioms entirely in favor of a bundled typeclass:
```lean
Delete the Bare Axioms. Remove `axiom intersectionForm` at Jacobians/Axioms/IntersectionForm.lean:59-62, as well as its companion axioms (`AX_IntersectionForm_alternating` and `AX_IntersectionForm_perfect`) from the same file.
```
However, both `AX_IntersectionForm_alternating` and `AX_IntersectionForm_perfect` assume their axiom declarations survive to be proven as top-level theorems via dedicated multi-month topology infrastructure projects:
```lean
5. **Replace with Theorem:** Change `axiom AX_IntersectionForm_alternating` to a `theorem` at `Jacobians/Axioms/IntersectionForm.lean:66`.
```
**Recommendation:** Choose between bundling the intersection form properties into the `HasIntersectionForm` typeclass (and canceling the 10-effort proofs) or keeping them as top-level `axiom`s to be individually proven.

## Finding 2 — Incompatible basepoint handling for `abelJacobiDiv`
**Plans involved:** `abelJacobiDiv`, `AX_AbelTheorem`
**Class:** signature
**Evidence:**
Plan `abelJacobiDiv` globally fixes the integration basepoint for the Abel-Jacobi map regardless of the input divisor:
```lean
noncomputable def abelJacobiDiv (X : Type u) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] : Divisor X →+ Jacobian X :=
  FreeAbelianGroup.lift (fun P => ofCurveImpl X (Classical.choice ‹Nonempty X›) P)
```
But Plan `AX_AbelTheorem` explicitly requires the integration basepoint to dynamically avoid the poles of the divisor being evaluated:
```lean
5. **⊆ direction, Step 4 (basepoint selection, with pole avoidance).** We need a basepoint `P₀ ∈ X` for the integral `∫_{P₀}^P ω̃_D`. **`P₀` must be chosen disjoint from `supp(D⁺) ∪ supp(D⁻)`**
```
**Recommendation:** Rework `abelJacobiDiv` to either take a generic non-pole basepoint as an explicit parameter or dynamically select it per-divisor, instead of using a global `Classical.choice` that breaks Abel's Theorem.

## Finding 3 — Conflicting implementations of path integration
**Plans involved:** `pathIntegralBasepointFunctional`, `AX_pathIntegral_local_antiderivative`, `bridgePath`
**Class:** duplicate
**Evidence:**
Plan `AX_pathIntegral_local_antiderivative` instructs the functional to be backed by the Kirov bridge:
```lean
1. **Discharge `pathIntegralBasepointFunctional` first** to a `def` per `pathIntegralBasepointFunctional.md` (redirect to `Jacobians.Bridge.kirovBackedFunctional`).
```
However, `pathIntegralBasepointFunctional` ignores the Kirov bridge entirely and builds a multi-chart integrator from scratch:
```lean
Define `pathIntegralAnalyticArc` by summing the existing primitive `pathIntegralOnChart`...
Define `pathIntegralBasepointFunctional` by evaluating `pathIntegralAnalyticArc` on the path retrieved from Step 1.
```
Consequently, `bridgePath` redundantly builds its own multi-chart infrastructure for the Kirov side:
```lean
2. Refine Cover with Convex Chart Balls ... 3. Flat-at-Endpoints Reparameterization ... Define `noncomputable def bridgePath (P₀ P : X) : ℝ → X`
```
**Recommendation:** Unify the integration backends by either fully redirecting `pathIntegralBasepointFunctional` to the Kirov line integral (relying on `bridgePath`), or deleting the Kirov bridge entirely in favor of `pathIntegralAnalyticArc`.

## Finding 4 — Duplicate topological instances for `Hyperelliptic`
**Plans involved:** `Hyperelliptic`, `Hyperelliptic-instTopologicalSpace`
**Class:** duplicate
**Evidence:**
Plan `Hyperelliptic` already handles the generation of the topological space instance natively in Step 3:
```lean
3. Construct the `TopologicalSpace` instance in term mode via `TopologicalSpace.induced (Equiv.cast <| dif_pos h) inferInstance`. Lift `Prop`-valued classes (`T2Space`, `CompactSpace`, `ConnectedSpace`, `Nonempty`) using `rw` / `simp only [Hyperelliptic]`.
```
Yet Plan `Hyperelliptic-instTopologicalSpace` treats this exact construction as a separate task:
```lean
3. Post-infra discharge: Define the unified topology structurally based on how the `Hyperelliptic` type is implemented:
   - If `Hyperelliptic` is a structure wrapping a `dite` or a dependent parity dispatch, define the instance by cases on `Odd H.f.natDegree` and use `TopologicalSpace.induced` mapping into the respective parity branch.
```
**Recommendation:** Delete the standalone `Hyperelliptic-instTopologicalSpace` plan, as its scope is entirely swallowed by the `Hyperelliptic` plan.

## Finding 5 — Divergent infrastructures for Abel-Jacobi injectivity
**Plans involved:** `AX_ofCurve_inj`, `AX_AbelTheorem`
**Class:** duplicate
**Evidence:**
Plan `AX_ofCurve_inj` proves injectivity (which is the $\mathcal{O}(P-Q)$ special case of Abel's Theorem) using the Exponential Sheaf Sequence:
```lean
relate the analytic Jacobian ... to $H^1(X, \mathcal{O}_X) / \text{im}(H^1(X, \mathbb{Z}))$. Under this identification, the exact sequence ... injects the Jacobian into $H^1(X, \mathcal{O}_X^\times)$, which is identified with the Picard group
```
Meanwhile, Plan `AX_AbelTheorem` proves the general theorem using analytic residue calculus and period normalization:
```lean
Apply Riemann–Roch (`AX_RiemannRoch`, `Jacobians/Axioms/RiemannRoch.lean:59`) and Serre duality ... to produce a meromorphic 1-form `ω_D` ... period adjustment via A-period normalization ... f(P) := exp(∫_{P₀}^P ω̃_D)
```
**Recommendation:** Consolidate the proof strategies to use a single mathematical foundation (either the Exponential Sheaf Sequence or the Forster residue route) for both theorems, rather than building two disjoint multi-month infrastructures to extract meromorphic functions from Abel-Jacobi roots.

CROSS-PLAN VERDICT: 5 findings (5 actionable) — We found severe structural collisions where plans overwrite each other's target declarations, duplicate multi-month topological and analytical infrastructures, and specify mathematically incompatible functional signatures for integration.
