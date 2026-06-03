# `canonicalDivisor` — discharge recipe

**Location:** `Jacobians/RiemannSurface/LineBundle.lean:123`
**Route:** needs-infra &nbsp;&nbsp; **Effort:** 10 &nbsp;&nbsp; **Est:** multi-month undertaking in Mathlib
**Blocked by:** `Divisor` (`Jacobians/RiemannSurface/LineBundle.lean:51`), `PrincipalDivisors` (`Jacobians/RiemannSurface/LineBundle.lean:70`), plus major missing Mathlib infrastructure for meromorphic sections of line bundles and the Identity Theorem.

**Statement (verbatim):**
```lean
/-- **Opaque axiom.** The canonical sheaf `Ω¹_X` is a line bundle,
represented by a distinguished divisor class `K : Divisor X` up to
linear equivalence. -/
axiom canonicalDivisor (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] : Divisor X
```

**Why it's an axiom right now:** Classically `K = div(ω)` for any nonzero meromorphic 1-form `ω` on `X`. Currently, this is stated as a `Type`-valued data axiom, which is problematic for definitional equality and typeclass inference. Discharging it requires immense missing Mathlib infrastructure: a robust API for meromorphic 1-forms (handling poles properly without pointwise junk values), the Identity Theorem to guarantee a finite number of zeros/poles on a compact surface, and the Riemann Existence Theorem (or Riemann-Roch) to guarantee a non-zero form actually exists.

**Proof recipe**

1. Stage 1 — Robust `MeromorphicOneForm X` API. The existing `HolomorphicOneForm X` at `Jacobians/RiemannSurface/OneForm.lean:148` uses point-wise cocycle conditions. A naive adaptation for meromorphic forms fails because functions to `ℂ` return junk values (often `0`) at poles, rendering equations like $f_i(x) = f_j(x) \cdot (dz_j/dz_i)(x)$ vacuously true or false. `MeromorphicOneForm X` must be built rigorously by enforcing the cocycle condition on a dense open set (punctured neighborhoods) or at the level of germs/fraction fields using `Jacobians/Vendor/Wallace/HolomorphicForms/VanishingOrder.lean:90`.

2. Stage 2 — Finiteness via Identity Theorem. Before summing orders into a divisor, we must prove the sum is finite. Prove that a non-zero meromorphic form on a compact connected surface has finitely many zeros and poles. This requires formalizing the Identity Theorem for meromorphic functions and utilizing the `CompactSpace X` assumption.

3. Stage 3 — Define `MeromorphicOneForm.div`. Define the local order of the 1-form in a chart (via `Jacobians/Vendor/Wallace/HolomorphicForms/VanishingOrder.lean:342`). Crucially, orders *add* ($ord(f \cdot g) = ord(f) + ord(g)$). The transition function for a 1-form is the Jacobian derivative of the coordinate change ($dz_j / dz_i$). Since chart transitions are local biholomorphisms, this derivative is nowhere-zero, meaning its order of vanishing is **exactly 0**. Therefore, $ord_{local}(f_i) = ord_{local}(f_j) + 0$, making the local order chart-independent. Combine with Stage 2 to yield a well-defined `Divisor X`.

4. Stage 4 — Existence and Refactor. The existence of a nonzero meromorphic 1-form on any compact Riemann surface requires Riemann-Roch or the Riemann Existence Theorem. To unblock the `Type`-valued data axiom immediately, introduce a focused `Prop`-valued existence axiom `AX_nonzero_meromorphic_one_form_exists X`. 

5. Stage 5 — Replace the axiom. Using `Classical.choice` on the nonempty type of nonzero meromorphic 1-forms (from step 4), replace the axiom at `Jacobians/RiemannSurface/LineBundle.lean:123` with:
   ```lean
   noncomputable def canonicalDivisor (X : Type*) [...] : Divisor X :=
     (Classical.choice (nonzero_meromorphic_one_form_exists X)).val.div
   ```
   This successfully refactors the data axiom into a `Prop`-backed definition.

6. Reference: Forster, *Lectures on Riemann Surfaces*, Ch. II §17 (canonical divisor `K = div(ω)`, well-defined modulo `PrincipalDivisors`), Ch. II §18 (existence of nonzero meromorphic differentials); Miranda *Algebraic Curves and Riemann Surfaces* Ch. IV §1.

**Files touched**
- `Jacobians/RiemannSurface/MeromorphicOneForm.lean` — NEW. Define meromorphic forms via dense open sets/germs, not naive point-wise cocycles.
- `Jacobians/Axioms/MeromorphicExistence.lean` — NEW. House the `Prop`-level `AX_nonzero_meromorphic_one_form_exists` axiom.
- `Jacobians/RiemannSurface/LineBundle.lean` — replace `axiom canonicalDivisor` (line 123) with a `noncomputable def` invoking `Classical.choice`.

**Acceptance**
- `lake build Jacobians.RiemannSurface.LineBundle` succeeds.
- `#print axioms canonicalDivisor` no longer lists `canonicalDivisor` (it will list the new `Prop`-valued existence axiom instead).
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; total axiom count remains the same, but data-axiom count drops by 1.

**Risk / escalation triggers**
- Attempting to use pointwise cocycles for meromorphic forms (like `OneForm.lean:120`) results in unprovable theorems at the poles due to junk values; escalate to a dense-open-set or germ-based approach immediately.
- Proving finiteness of zeros/poles is completely blocked if the Mathlib Identity Theorem for meromorphic functions is missing or inapplicable to manifolds.

**`Gemini critique addressed:`**
- Reclassified route to `needs-infra` and recalibrated Effort to `10` / "multi-month undertaking", acknowledging the massive gap in Mathlib for meromorphic sections and the Identity Theorem.
- Corrected the mathematical description of chart-independence in Stage 3: explicitly stated that orders *add* and that the transition derivative is a biholomorphism with an order of exactly 0.
- Replaced the naive cocycle adaptation in Stage 1 with a robust requirement for dense open sets or germs to prevent junk-value errors at poles.
- Removed the handwaving of `.toFinset` in Stage 2, explicitly making the formalization of the Identity Theorem and compactness a prerequisite for the divisor sum.

## Sub-plans needed
- `MeromorphicOneForm_API.md` — Building the robust API for meromorphic 1-forms avoiding pointwise junk values (via dense open sets or germs).
- `Meromorphic_Identity_Theorem.md` — Formalizing the Identity Theorem for meromorphic functions on compact manifolds to guarantee finite zeros/poles.

---
**Vetting trail.** Critique: `_vetting/canonicalDivisor.md`. Verdict: reject. Revised: 2026-06-03.

**Cross-plan patch (2026-06-03):** Standardised manifold-model-space notation to `𝓘(ℂ, ℂ)` (Mathlib's `modelWithCornersSelf ℂ ℂ`); the single-arg alias `𝓘(ℂ)` caused typeclass-unification failures between generic and concrete plans.
