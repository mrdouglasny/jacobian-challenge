# Cross-plan consistency audit — 31 `provable-from-other-axioms` plans

**Model:** gemini-3.1-pro-preview  (extended thinking)
**Duration:** 168.9s
**Plans audited:** 31
**Date:** 2026-06-03

---

## Finding 1 — Signature split on Hyperelliptic equivalences
**Plans involved:** `AX_Hyperelliptic_genus`, `AX_Hyperelliptic_oddEquiv`
**Class:** signature
**Evidence:**
In `AX_Hyperelliptic_genus`:
```lean
1. **Equivalence Upgrade:** Redefine `AX_Hyperelliptic_oddEquiv` (`Hyperelliptic.lean:93`) and `AX_Hyperelliptic_evenEquiv` (`Hyperelliptic.lean:99`) to be biholomorphisms instead of simple `Homeomorph`s.
```
In `AX_Hyperelliptic_oddEquiv`:
```lean
theorem AX_Hyperelliptic_oddEquiv (H : HyperellipticData) (h : Odd H.f.natDegree) :
    Hyperelliptic H ≃ₜ HyperellipticOdd H h
```
and its plan explicitly constructs this as a topological `Homeomorph` via `Equiv.cast` with `continuous_toFun` / `continuous_invFun` fields, not as an analytic biholomorphism.
**Recommendation:** Keep the equivalences as `Homeomorph`s (as dependent topology casts are difficult enough) and require `AX_Hyperelliptic_genus` to promote them locally using a manifold transport lemma, rather than changing the base equivalence signatures.

## Finding 2 — Signature split on H1 group operation
**Plans involved:** `AX_Elliptic_H1_symplectic`, `loopIntegralToH1`
**Class:** signature
**Evidence:**
In `AX_Elliptic_H1_symplectic`:
```lean
Define `H1 X x₀ := Abelianization (FundamentalGroup X x₀)`.
```
and it relies on this definition to build a `Module.Basis (Fin 2) ℤ (H1 (Elliptic ω₁ ω₂ h) 0)`.
In `loopIntegralToH1`:
```lean
The H₁ target is `Additive (Abelianization (FundamentalGroup X x₀))` (`Homology.lean:41-42`), so the descent is `π₁ →* Multiplicative (ℂ-dual) → Abelianization → Additive`.
```
Mathlib's `Abelianization` yields a multiplicative `CommGroup`, whereas `Module.Basis` over `ℤ` strictly requires an `AddCommGroup`. `loopIntegralToH1` correctly identifies the need for the `Additive` wrapper, while `AX_Elliptic_H1_symplectic` defines it purely multiplicatively, breaking the `Module` typeclass requirement.
**Recommendation:** Update `AX_Elliptic_H1_symplectic` to define `H1 X x₀ := Additive (Abelianization (FundamentalGroup X x₀))` to align with `loopIntegralToH1` and Lean's `Module` requirements.

## Finding 3 — Signature split on Riemann-Roch formulation
**Plans involved:** `AX_curve_generates_jacobian`, `AX_RiemannRoch`
**Class:** signature
**Evidence:**
In `AX_RiemannRoch`, the axiom is explicitly typed using $H^1$:
```lean
    (Module.finrank ℂ (H0 (LineBundle.ofDivisor D)) : ℤ) -
    (Module.finrank ℂ (H1 (LineBundle.ofDivisor D)) : ℤ) =
      Divisor.deg X D + 1 - (genus X : ℤ)
```
In `AX_curve_generates_jacobian`, the plan assumes the theorem outputs the $H^0(K - E)$ formulation, having explicitly removed the `AX_SerreDuality` step that would bridge them:
```lean
Apply `AX_RiemannRoch` (`Jacobians/Axioms/RiemannRoch.lean:61-66`) to `E`:
h⁰(O(E)) − h⁰(O(K − E)) = deg E + 1 − g = 1
```
And claims:
```markdown
- **Removed irrelevant Serre Duality step:** Completely dropped the former Step 3 regarding the genericity and uniqueness of the effective divisor via Serre Duality...
```
Without `AX_SerreDuality` to convert $H^1(\mathcal{O}(E))$ to $H^0(\mathcal{O}(K - E))^*$, the algebraic reduction in `AX_curve_generates_jacobian` is impossible because it does not match the signature of `AX_RiemannRoch`.
**Recommendation:** Restore the `AX_SerreDuality` prerequisite in `AX_curve_generates_jacobian` so it can mathematically bridge the $H^1$ signature of `AX_RiemannRoch` to the $H^0(K-E)$ formulation needed for its proof.

## Finding 4 — Mathlib-decl drift on PartialHomeomorph
**Plans involved:** `affineLiftProjY_compat_infinityChart`, `infinityChart`
**Class:** drift
**Evidence:**
In `affineLiftProjY_compat_infinityChart`:
```markdown
- **Corrected Mathlib namespace:** Removed references to the hallucinated `OpenPartialHomeomorph` namespace, replacing them with standard `PartialHomeomorph` / local dot-notation.
```
and applies it as:
```lean
Using `PartialHomeomorph.trans_apply`, `lift_openEmbedding_apply`...
```
However, the other OA2 chart plans still enforce the stale `OpenPartialHomeomorph` name. For example, in `infinityChart`:
```lean
Bundle into `OpenPartialHomeomorph (HyperellipticOdd H h) ℂ`. Mathlib's `OpenPartialHomeomorph` (`.lake/packages/mathlib/Mathlib/Topology/OpenPartialHomeomorph/Basic.lean`) requires...
```
**Recommendation:** Update all OA2 chart plans (`infinityChart`, `affineLiftProjX_compat_infinityChart`, `infinityChart_compat_affineLiftProjX`, `infinityChart_compat_affineLiftProjY`) to use the modern `PartialHomeomorph` Mathlib namespace, removing the stale `OpenPartialHomeomorph` references.

CROSS-PLAN VERDICT: 4 findings (4 actionable) — The cluster shows critical signature splits around manifold equivalences, topological group types, and Serre duality, alongside a namespace drift for partial homeomorphisms.
