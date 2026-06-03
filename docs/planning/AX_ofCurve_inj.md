# `AX_ofCurve_inj` — discharge recipe

**Location:** `Jacobians/Axioms/AbelJacobiMap.lean:257`
**Route:** needs-infra &nbsp;&nbsp; **Effort:** 9 &nbsp;&nbsp; **Est:** Specialized to the `D = P − Q` case of `AX_AbelTheorem`; resource budget folds into the residue-and-period infrastructure already estimated there (~9–18 months, dominated by `MeromorphicForms` + `BoundaryStokes` + `PunctureLimits` + `Residues`).
**Blocked by:** `AX_RiemannRoch`, `AX_SerreDuality`, `AX_RiemannBilinear`, `AX_AnalyticCycleBasis`, `AX_PeriodLattice`, and the new residue-infrastructure files `Jacobians/RiemannSurface/MeromorphicForms.lean`, `BoundaryStokes.lean`, `PunctureLimits.lean`, `Residues.lean` (all introduced in `AX_AbelTheorem.md`).

**Statement (verbatim):**
```lean
/-- **Axiom (= Abel's theorem, curve side).** The Abel-Jacobi map is
injective when `genus X > 0`. -/
axiom AX_ofCurve_inj {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] (P : X) (_h : 0 < genus X) :
    Function.Injective (ofCurveImpl X P)
```

**Why it's an axiom right now:** This is the **point-level / curve side of Abel's theorem**: for a compact Riemann surface `X` of positive genus, the Abel-Jacobi map `P ↦ (∫_{P₀}^P ω_i)_i mod periods` is injective. Equivalently, two distinct points `P, Q ∈ X` are never linearly equivalent as degree-1 divisors, because `dim H⁰(X, O(P)) = 1`. The required step is to construct a meromorphic function from analytic period data, bridging the analytic Jacobian and the algebraic Picard group. The construction is the `D = P − Q` special case of the `⊆` direction of `AX_AbelTheorem` (Forster §21), so we discharge it as a corollary of that plan rather than via a parallel sheaf-cohomology infrastructure.

**Proof recipe**

Per the cross-plan patch (2026-06-03), this recipe is now **consolidated onto the Forster residue + period-normalization route**, exactly the route used by `AX_AbelTheorem.md`. The previous Exponential Sheaf Sequence (EES) path is retired; see "Strategy change" below. The unified plan reuses the residue-theorem infrastructure (`MeromorphicForms.lean`, `BoundaryStokes.lean`, `PunctureLimits.lean`, `Residues.lean`) and the period-normalization machinery introduced in `AX_AbelTheorem.md`.

1. **Unfold the injectivity hypothesis as a degree-0 Abel-Jacobi vanishing.** Suppose `ofCurveImpl X P₀ P = ofCurveImpl X P₀ Q` for distinct `P, Q ∈ X`. Unfolding `ofCurveImpl` (`Jacobians/Axioms/AbelJacobiMap.lean:229–233`) and using `AX_ofCurve_self`, this is equivalent to the vector `(∫_Q^P ω_1, …, ∫_Q^P ω_g) ∈ ℂ^g` lying in the period lattice `Λ`. Equivalently, the degree-0 divisor `D := P − Q` satisfies `abelJacobiDivAt X P₀ D = 0` in `Jacobian X`. Choose a basepoint `P₀ ∉ {P, Q}` via the same pole-avoidance construction as `AX_AbelTheorem.md` Step 5 (the finite-set / open-dense complement argument). This invokes the explicit-basepoint variant `abelJacobiDivAt` introduced by the cross-plan patch to `abelJacobiDiv.md`.
2. **Apply the `⊆` direction of `AX_AbelTheorem` to `D = P − Q`.** Once `AX_AbelTheorem` is discharged (or, during the staged build-up, once its Steps 3–6 are available as a private lemma `AbelInversion`), the hypothesis `abelJacobiDivAt X P₀ D = 0` produces a meromorphic function `g : X → ℂ ∪ {∞}` with `div g = D = P − Q`. The construction is precisely `g(P) := exp(∫_{P₀}^P ω̃_D)` where `ω̃_D` is the A-period-normalized third-kind differential with simple poles `+1` at `P` and `−1` at `Q` (Forster §21, Riemann–Roch + Serre duality applied to `𝒪(P + Q) ⊗ K_X`).
3. **Riemann–Roch + Serre duality bound on `h⁰(𝒪(P))`.** With `g ∈ H⁰(X, 𝒪(P)) ∖ H⁰(X, 𝒪)` exhibited (since `div g + P = Q + (P − Q) + P = 2P ≥ 0` shows `g ∈ H⁰(𝒪(P))` and `g` is non-constant), we have `h⁰(𝒪(P)) ≥ 2`. Apply `AX_RiemannRoch` (`Jacobians/Axioms/RiemannRoch.lean:59`) to `𝒪(P)`:
   ```
   h⁰(𝒪(P)) − h¹(𝒪(P)) = deg(P) + 1 − g = 2 − g
   ```
   and `AX_SerreDuality` (`Jacobians/Axioms/SerreDuality.lean:54`) to identify `h¹(𝒪(P)) = h⁰(K − P) ≤ h⁰(K) − 1 = g − 1` for genus `> 0`. This forces `h⁰(𝒪(P)) ≤ 1`, contradicting `h⁰(𝒪(P)) ≥ 2`. Therefore `P = Q`.
4. **Replace `axiom` with `theorem`.** Execute the discharge in `Jacobians/Axioms/AbelJacobiMap.lean:257`. The proof body is a corollary of the `⊆` direction of `AX_AbelTheorem` plus a 10-line `AX_RiemannRoch` / `AX_SerreDuality` numerology lemma.

**Strategy change (Cross-plan patch 2026-06-03; supersedes the original EES recipe).** The earlier draft (now retired) extracted the meromorphic function `g` via the Exponential Sheaf Sequence `0 → ℤ_X → 𝒪_X → 𝒪_X^× → 0` and its connecting homomorphism to `Pic(X)`. That path is **disjoint** from the residue/period infrastructure built by `AX_AbelTheorem` and would require Mathlib-level sheaf cohomology for complex manifolds (Čech cohomology of holomorphic-sheaf data, plus the analytic-Jacobian ↔ `H¹(𝒪)/H¹(ℤ)` identification) that is multiple person-years downstream. The Forster route used by `AX_AbelTheorem.md` reaches the same conclusion through residue calculus and period normalization — infrastructure that is already partially specified and required regardless. Consolidating the two onto a single route saves an entire parallel infrastructure project. Steps 2–6 of `AX_AbelTheorem.md` are now reused with `D := P − Q`, and Step 3 above is the only `AX_ofCurve_inj`-specific tail.

**Files touched**
- `Jacobians/Axioms/AbelJacobiMap.lean` — replace `axiom AX_ofCurve_inj` (line 257) with `theorem`; body is a thin corollary of `AX_AbelTheorem` plus a Riemann–Roch / Serre-duality numerology lemma.
- *(Removed)* `Jacobians/RiemannSurface/ExponentialSequence.lean` and `Jacobians/RiemannSurface/AbelTheorem.lean` are **no longer introduced** by this plan; meromorphic-function extraction is delegated to the residue infrastructure introduced by `AX_AbelTheorem.md` (`MeromorphicForms.lean`, `BoundaryStokes.lean`, `PunctureLimits.lean`, `Residues.lean`).

**Acceptance**
- `lake build Jacobians.Axioms.AbelJacobiMap` succeeds.
- `#print axioms Jacobians.Challenge.<downstream theorem consuming injectivity>` no longer lists `AX_ofCurve_inj`.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1.

**Risk / escalation triggers**
- **`AX_AbelTheorem` slips or stalls.** This recipe is now a corollary of `AX_AbelTheorem`'s `⊆` direction; if that plan stalls on the residue infrastructure (`BoundaryStokes.lean`, `PunctureLimits.lean`, `Residues.lean`), `AX_ofCurve_inj` is automatically blocked. Escalate jointly.
- **`abelJacobiDivAt` refactor in `abelJacobiDiv.md` not landed.** Step 1 uses the explicit-basepoint variant. Escalate if `abelJacobiDiv` is still defined only via `Classical.choice` at the point this recipe runs.
- **`Divisor` / `LineBundle` layer not landed.** Step 3's invocation of `AX_RiemannRoch` and `AX_SerreDuality` requires the `Divisor` / `LineBundle` types. Escalate if these are not formalized yet.
- **Mumford theta-divisor fallback.** If, against expectation, the residue infrastructure overshoots its budget while the Mumford theta route in `AX_AbelTheorem.md` becomes viable instead, switch this recipe to consume the Mumford-route lemma exporting `D → meromorphic g` rather than the Forster one — the Step 3 numerology tail is unchanged.

### Gemini critique addressed
- Reclassified route to `needs-infra` and updated estimates to reflect the necessity of residue/period infrastructure (consumed from `AX_AbelTheorem.md`) rather than a trivial and faulty algebraic reduction.
- Scrapped the logically flawed steps from the original recipe that treated an open 1-chain as a closed 1-cycle and misapplied Riemann's bilinear relations to non-closed paths.
- **Cross-plan patch (2026-06-03):** Replaced the Exponential Sheaf Sequence (EES) construction of the meromorphic function `g` with the Forster residue + A-period-normalization construction (`g = exp(∫ ω̃_D)`), aligning with `AX_AbelTheorem.md`. The earlier EES path required a multi-month sheaf-cohomology infrastructure disjoint from the residue infrastructure already required for `AX_AbelTheorem`; consolidating onto Forster eliminates the duplicated foundation.

## Sub-plans needed
- *(Retired)* `INFRA_ExponentialSequence.md` is **no longer a prerequisite** of this plan under the unified Forster strategy.
- Consumes (does not introduce) the residue infrastructure from `AX_AbelTheorem.md`: `MeromorphicForms.lean`, `BoundaryStokes.lean`, `PunctureLimits.lean`, `Residues.lean`.
- Consumes the explicit-basepoint variant `abelJacobiDivAt` from the revised `abelJacobiDiv.md`.

---
**Vetting trail.** Critique: `_vetting/AX_ofCurve_inj.md`. Verdict: reject. Revised: 2026-06-03.

**Cross-plan patch (2026-06-03):** Standardised manifold-model-space notation to `𝓘(ℂ, ℂ)` (Mathlib's `modelWithCornersSelf ℂ ℂ`); the single-arg alias `𝓘(ℂ)` caused typeclass-unification failures between generic and concrete plans.

**Cross-plan patch (2026-06-03):** Retired the Exponential Sheaf Sequence route and re-derived `AX_ofCurve_inj` as the `D = P − Q` corollary of `AX_AbelTheorem`'s Forster residue + period-normalization recipe, unifying both proofs on the residue/period infrastructure introduced by `AX_AbelTheorem.md`.
