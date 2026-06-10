# `AX_Elliptic_H1_symplectic` — discharge recipe

**Location:** `Jacobians/ProjectiveCurve/Elliptic/Witnesses.lean:166`
**Route:** needs-infra, provable-from-other-axioms &nbsp;&nbsp; **Effort:** 7 &nbsp;&nbsp; **Est:** ~3–6 focused weeks for covering space / fundamental group infra, ~300 LOC
**Blocked by:** `AX_IntersectionForm_alternating`, `AX_IntersectionForm_perfect`, `intersectionForm`, `AX_AnalyticCycleBasis` (the structure target itself); transitively the project's homology layer (`H1`, `Path.toHomologyClass`, the covering-space description of `π₁(ℂ/Λ)`)

**Statement (verbatim):**
```lean
axiom AX_Elliptic_H1_symplectic :
    AnalyticCycleBasis (Elliptic ω₁ ω₂ h) 0
```

**Why it's an axiom right now:** `AnalyticCycleBasis X x₀` (`Jacobians/Axioms/AnalyticCycleBasis.lean:220-242`) packages three things: (i) `2 * genus X` analytic loops, (ii) a ℤ-basis of `H1 X x₀` of size `2 * genus X`, and (iii) a symplectic intersection-form matrix `[[0, I], [-I, 0]]` in that basis. For an elliptic curve `genus = 1` (`genus_Elliptic_eq_one` at `Jacobians/ProjectiveCurve/Elliptic/OneForm.lean:195`, surfaced as `AX_genus_Elliptic_eq_one` at `Elliptic/Genus.lean:45-48`), so we need 2 loops, a rank-2 basis of `H1`, and the relations `⟨A,A⟩ = ⟨B,B⟩ = 0`, `⟨A,B⟩ = 1`. The two loops `aLoop` and `bLoop` are already built (`Witnesses.lean:123-140` and `:143-160`), but discharging this structure requires a hybrid approach: building a real basis using Mathlib's fundamental group/covering spaces, and bypassing the formal impossibility of computing the uninterpreted global `intersectionForm` via a scoped helper axiom.

**Proof recipe**

This discharge uses a hybrid strategy. First, we define `H1` purely algebraically via fundamental groups to genuinely prove the `isBasis` field using Mathlib's covering spaces. Second, since `intersectionForm` is currently an uninterpreted, opaque axiom, we isolate the missing singular homology theory by introducing a single integer-equality helper axiom to satisfy the `symplectic` field.

### Phase 1 — Homology infrastructure (prereq)

1. **Define `H1` and `Path.toHomologyClass`.** Rather than waiting on singular homology, define `H1 X x₀ := Additive (Abelianization (FundamentalGroup X x₀))`. The `Additive` wrapper is essential: Mathlib's `Abelianization` yields a multiplicative `CommGroup`, but `Module ℤ` (required for `Module.Basis (Fin 2) ℤ (H1 _)` in step 4) strictly requires an `AddCommGroup`. The `Additive` wrapper supplies that `AddCommGroup` instance, letting all downstream `Module`/`Basis` typeclasses elaborate. Define `Path.toHomologyClass` by composing the standard quotient map from paths to `FundamentalGroup`, the quotient map to `Abelianization`, and `Additive.ofMul`. This matches the canonical type fixed by `loopIntegralToH1` (see `Jacobians/RiemannSurface/Homology.lean:41-42`) and addresses the TODOs referenced in `Jacobians/Axioms/AnalyticCycleBasis.lean:244-249`.
2. **Covering-space description of `H1 (ℂ/Λ) 0`.** Use Mathlib's `Mathlib.Topology.Covering` API. For a complex torus `T = ℂ/Λ`, the universal cover is `ℂ` (simply connected), giving an isomorphism `FundamentalGroup T 0 ≃ Λ`. Since `Λ` is already abelian, the abelianization is trivial. Transport this through to prove `H1 T 0 ≃ Λ ≃ ℤ²` for `Λ = ℤω₁ + ℤω₂`. (Mathematical references for this canonical identification: Mumford, *Tata Lectures on Theta I*, Ch. II §2; Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §4).

### Phase 2 — Discharge on `Elliptic` (post-infra)

3. **Specialize `genus`.** `genus_Elliptic_eq_one` (`Jacobians/ProjectiveCurve/Elliptic/OneForm.lean:195`) gives `genus (Elliptic ω₁ ω₂ h) = 1`, so `2 * genus _ = 2` and `Fin (2 * genus _) ≃ Fin 2`. Use this `Equiv` (call it `e2`) to map the two loops into the indexed `loops` field.
4. **`isBasis` field.** Construct a `Module.Basis (Fin 2) ℤ (H1 (Elliptic ω₁ ω₂ h) 0)`. Because `H1` is now `Additive (Abelianization (FundamentalGroup _ _))`, the requisite `AddCommGroup` and `Module ℤ` instances elaborate automatically (every `AddCommGroup` is canonically a `ℤ`-module via `AddCommGroup.toIntModule`). The basis is the image of `(aLoop, bLoop)` under `Path.toHomologyClass`. Genuinely prove this is a basis by transporting `Pi.basisFun ℤ (Fin 2)` through the iso `H1 (Elliptic _) 0 ≃ ℤ²` established via covering spaces in Step 2 — note that the iso is now an `AddEquiv` (between additive groups) rather than a `MulEquiv`, since the `Additive` wrapper is in play on the LHS. Use `Module.Basis.ofEquivFun` or `Module.Basis.map`.
5. **Introduce Helper Axiom.** Because the global `intersectionForm` has no definitional equations, Lean cannot evaluate it. Introduce a tightly scoped helper axiom in `Witnesses.lean`:
   ```lean
   axiom AX_Elliptic_intersection_A_B : intersectionForm 0 (Path.toHomologyClass (aLoop ω₁ ω₂ h)) (Path.toHomologyClass (bLoop ω₁ ω₂ h)) = 1
   ```
6. **Assemble `AnalyticCycleBasis` and `symplectic` field.** Construct the structure (`Jacobians/Axioms/AnalyticCycleBasis.lean:220-242`). For `i, j : Fin 1`, `αEmbed i = ⟨0, _⟩` and `βEmbed i = ⟨1, _⟩` (`AnalyticCycleBasis.lean:198-208`).
   - Use `AX_IntersectionForm_alternating` (`Jacobians/Axioms/IntersectionForm.lean:66-70`) to supply the formally proven equalities `intersectionForm 0 A A = 0` and `intersectionForm 0 B B = 0`.
   - Use the explicit helper `AX_Elliptic_intersection_A_B` to provide `intersectionForm 0 A B = 1`.
   - (`AX_IntersectionForm_perfect` at `Jacobians/Axioms/IntersectionForm.lean:91-95` is the mathematical justification for why this matrix form gives a unimodular pairing, but is not needed for the entry-by-entry verification here).
7. **Replace `axiom` with `theorem`.** At `Jacobians/ProjectiveCurve/Elliptic/Witnesses.lean:166-167`, turn `AX_Elliptic_H1_symplectic` into a proven theorem. Update `ellipticCycleBasis` (`Witnesses.lean:173-174`) to use the new construction directly.

**Files touched**
- `Jacobians/ProjectiveCurve/Elliptic/Witnesses.lean` — replace `axiom AX_Elliptic_H1_symplectic` (lines 166–167) with a `theorem`; add `axiom AX_Elliptic_intersection_A_B`; rewrite `ellipticCycleBasis` (lines 173–174) to use the new construction.
- `Jacobians/RiemannSurface/Homology.lean` (or a new sibling) — add `H1` definition via `Abelianization (FundamentalGroup _)` and `Path.toHomologyClass`.
- `Jacobians/AbelianVariety/ComplexTorusHomology.lean` — genuine fundamental group and covering-space proofs showing the rank-2 basis of `H1 (ℂ/Λ) 0` maps to `(ω₁, ω₂)`.

**Acceptance**
- `lake build Jacobians.ProjectiveCurve.Elliptic.Witnesses` succeeds.
- `#print axioms Jacobians.ProjectiveCurve.ellipticCycleBasis` no longer lists `AX_Elliptic_H1_symplectic` (though it will list the new `AX_Elliptic_intersection_A_B` helper).
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; net monolithic axiom count goes down (trading a massive structure axiom for a single integer-equality axiom).

**Risk / escalation triggers**
- If Mathlib's `FundamentalGroup` or `Covering` API is insufficiently developed to support extracting the discrete lattice from the universal cover `ℂ → ℂ/Λ`, escalate.
- If the orientation / sign convention for `intersectionForm` in `Jacobians/Axioms/IntersectionForm.lean` is not aligned with the `Im(ω̄₁ ω₂) > 0` convention from Griffiths–Harris Ch. 0.4, the math backing `AX_Elliptic_intersection_A_B` may require a sign-flip. Escalate the orientation choice to ensure consistency across the codebase.
- If `genus_Elliptic_eq_one` ever changes signature (e.g. becomes a `genus_Elliptic_eq` returning an arbitrary `Nat`), the `Fin (2 * genus _) ≃ Fin 2` step needs adjustment; escalate to keep this recipe in sync.

### Gemini critique addressed:
- Reclassified the Route to a hybrid `needs-infra, provable-from-other-axioms` and adjusted the Estimate to reflect bounding the effort strictly to covering space theory.
- Replaced the vague future "homology layer" with a formal and concrete definition: `H1 X x₀ := Additive (Abelianization (FundamentalGroup X x₀))` (the `Additive` wrapper is needed so the `Module ℤ` / `Basis` typeclasses elaborate; see Step 1).
- Replaced the formally impossible goal of computing the opaque `intersectionForm` function by introducing a tightly scoped integer-equality helper axiom (`AX_Elliptic_intersection_A_B`).
- Explicitly stated that `AX_IntersectionForm_alternating` will be used for the diagonal `⟨A, A⟩ = 0` and `⟨B, B⟩ = 0` cases in the symplectic field proof.

---
**Vetting trail.** Critique: `_vetting/AX_Elliptic_H1_symplectic.md`. Verdict: reject. Revised: 2026-06-03.

**Cross-plan patch (2026-06-03):** H1 type canonicalised to `Additive (Abelianization (FundamentalGroup X x₀))` so `Module ℤ` typeclasses elaborate.
---

## D1 re-type + discharge attempt (2026-06-10, feat/period-cycle-basis)

The D1 merge (`PeriodCycleBasis` replacing `AnalyticCycleBasis`, see
`docs/planning/CYCLEBASIS_ALTERNATIVES.md` §1) re-typed this axiom to
`PeriodCycleBasis (Elliptic ω₁ ω₂ h) 0`. **Attempted full discharge;
outcome: NOT closable yet — the axiom was not only needed for the
symplectic field.** Field-by-field:

| Field | Status after D1 |
|---|---|
| `loops` | constructible (`aLoop`/`bLoop`, analyticity discharged d4f6e82) |
| `R1` | now **provable**: form space is 1-dim (`eq_smul_ellipticDz`), so `Q(P(η),P(ζ)) = c·c'·(AB−BA) = 0` |
| `R2` | now **provable** modulo computing `∫_a dz = ω₁`, `∫_b dz = ω₂` (the lift-FTC machinery of `Elliptic/OfCurveInj.lean` does this for bridge paths; loop version is mechanical) + orienting the pair by `sign Im(ω₂/ω₁)` |
| `isBasis`, `loops_to_basis` | **still blocked**: needs `H₁(ℂ/Λ) ≅ ℤ²` with the A/B classes as generators, i.e. `π₁(ℂ/Λ) ≅ Λ` via covering-space theory (`ComplexTorus.isCoveringMap_quotient` exists, but the deck-group/π₁ identification does not) — exactly steps 1–4 of the recipe above |

So the D1 re-type strictly *shrank* the axiom's real content: the
previously-unprovable-by-design symplectic field (opaque
`intersectionForm`) is gone, the planned helper axiom
`AX_Elliptic_intersection_A_B` is no longer needed, and what remains is
precisely the covering-space H₁ computation (steps 1–4). The recipe's
steps 5–6 (symplectic verification through the intersection-form axioms)
are obsolete — replace with the R1/R2 computations sketched in the
axiom's docstring (`Witnesses.lean`).

Axiom retained (count unchanged by this attempt); satisfiability of the
re-typed statement argued in the docstring (orientation freedom absorbs
the `Im(ω₂/ω₁)` sign).
