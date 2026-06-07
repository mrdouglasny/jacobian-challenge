# `loopIntegralToH1` — discharge recipe

**Location:** `Jacobians/RiemannSurface/PathIntegral.lean:101`
**Route:** provable-from-other-axioms &nbsp;&nbsp; **Effort:** 4 &nbsp;&nbsp; **Est:** ~3 focused days, ~200 LOC
**Blocked by:** pathIntegralAnalyticArc, homotopyInvariance

**Statement (verbatim):**
```lean
axiom loopIntegralToH1 {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] (x₀ : X) :
    H1 X x₀ →+ (HolomorphicOneForm X →ₗ[ℂ] ℂ)
```

**Why it's an axiom right now:** The docstring (`PathIntegral.lean:90-100`) packages three classical subfacts into one axiom: (i) multi-chart path integration along piecewise-real-analytic loops (extending `pathIntegralOnChart` at `PathIntegral.lean:78-83`); (ii) homotopy invariance of `∫_γ ω` via Cauchy's theorem on chart disks + Stokes on the homotopy rectangle, which is what lets the integral descend to `H_1`; (iii) ℂ-linearity in `ω`. None of (i)–(iii) is presently formalized — `pathIntegralOnChart` is the only honest `def`. The H₁ target is `Additive (Abelianization (FundamentalGroup X x₀))` (`Homology.lean:41-42`), so the descent is `π₁ →* Multiplicative (ℂ-dual) → Abelianization → Additive`. Load-bearing for `periodMap` (`Periods.lean:39-43`), which currently has no other route.

> **Canonical H1 type definition.** This plan (and its companion `Jacobians/RiemannSurface/Homology.lean:41-42`) fixes the canonical type
> `H1 X x₀ := Additive (Abelianization (FundamentalGroup X x₀))`.
> The `Additive` wrapper is required so that `H1` carries an `AddCommGroup` instance (and hence a `Module ℤ` instance), which downstream consumers like `Module.Basis (Fin n) ℤ (H1 _)` and `AddMonoidHom`-valued constructions depend on. **Any other plan that defines or constructs into `H1` must use the same `Additive` wrapper** — in particular, see the cross-plan patch in `AX_Elliptic_H1_symplectic.md` (2026-06-03), which aligned that recipe to this canonical signature.

**Proof recipe**

The construction focuses strictly on the algebraic descent, assuming `pathIntegralAnalyticArc` and `homotopyInvariance` are available as axioms. 

1. **(P1 prereq) Multi-chart integration on a single arc.** Rely on `pathIntegralAnalyticArc`. The output is a `noncomputable def`
   ```
   pathIntegralAnalyticArc : AnalyticArc X → HolomorphicOneForm X → ℂ
   ```
   in `PathIntegral.lean`, generalizing `pathIntegralOnChart` (`PathIntegral.lean:78-83`) via a chart cover subordinate to the existing partition (`AnalyticArc.partition`, `AnalyticArc.lean:74-77`) plus the cotangent cocycle on `ω` (the `SatisfiesCotangentCocycle` field referenced at `PathIntegral.lean:30`). Mathlib primitives: `intervalIntegral` (used at `PathIntegral.lean:80`), `curveIntegral` (`MeasureTheory.Integral.CurveIntegral.Basic`, referenced at `PathIntegral.lean:50-51` and `AnalyticArc.lean:11`), `intervalIntegral.integral_add_adjacent_intervals` (already used in the Kirov vendor at `Vendor/Kirov/LineIntegral.lean:442`).

2. **(P1) Specialize to loops.** Introduce a `def pathIntegralAnalyticLoop (γ : AnalyticLoop X x₀) (ω : HolomorphicOneForm X) : ℂ` as `pathIntegralAnalyticArc γ.arc ω`, where `AnalyticLoop` is the structure at `AnalyticArc.lean:95-99`. Show ℂ-linearity in `ω` by unfolding to `intervalIntegral` and citing `intervalIntegral.integral_add` and `intervalIntegral.integral_const_mul` (compare the linearity lemmas at `Vendor/Kirov/LineIntegral.lean:108`, `:122`, `:134`).

3. **(P2–P3 prereq) Invoke Homotopy invariance.** Assume `homotopyInvariance` as an axiom (whose proof is relegated to a separate infrastructure plan):
   ```
   homotopyInvariance : ∀ (γ γ' : AnalyticLoop X x₀) (ω : HolomorphicOneForm X),
       Path.Homotopic γ.toPath γ'.toPath →
       pathIntegralAnalyticLoop γ ω = pathIntegralAnalyticLoop γ' ω
   ```

4. **(P4) Loop concatenation and π₁ structure.** Define `AnalyticLoop.concat (γ δ : AnalyticLoop X x₀) : AnalyticLoop X x₀` using the existing TODO at `AnalyticArc.lean:101-103` (scaled-union partition). Prove
   ```
   pathIntegralAnalyticLoop (γ.concat δ) ω
       = pathIntegralAnalyticLoop γ ω + pathIntegralAnalyticLoop δ ω
   ```
   via `intervalIntegral.integral_add_adjacent_intervals` (template at `Vendor/Kirov/LineIntegral.lean:442`). *Crucially*, doing this in local charts requires non-trivial affine change-of-variables (`intervalIntegral_comp_mul_add`) mapped through chart coordinate derivatives to handle the rescaling on `[0, 1/2]` and `[1/2, 1]`. Likewise `AnalyticLoop.reverse` (`AnalyticArc.lean:105`) with `intervalIntegral.integral_comp_sub_left` (`Vendor/Kirov/LineIntegral.lean:238`) for `∫_{γ⁻¹} ω = -∫_γ ω`.

5. **(P4) Build the group hom `π₁ → Multiplicative (ℂ-dual)`.** Use the Axiom of Choice to pick a piecewise-real-analytic representative for each element of `FundamentalGroup X x₀` (invoking `AX_AnalyticCycleBasis` at `Axioms/AnalyticCycleBasis.lean:257`, which affirms every class has an analytic representative). Define the map by evaluating `pathIntegralAnalyticLoop` on this `chosenRep g`. Bypassing `Quotient.lift` avoids needing a systematic analytic approximation for arbitrary continuous paths.
   ```
   loopIntegralOnFundGrp : FundamentalGroup X x₀ →* Multiplicative (HolomorphicOneForm X →ₗ[ℂ] ℂ)
   ```
   Sketch:
   ```lean
   apply MonoidHom.mk
   · intro g
     exact Multiplicative.ofAdd ⟨fun ω => pathIntegralAnalyticLoop (chosenRep g) ω, ..., ...⟩ -- ℂ-linearity from step 2
   · -- map_one: chosenRep 1 is continuously homotopic to the constant loop. Apply homotopyInvariance, then intervalIntegral.integral_zero (Vendor/Kirov/LineIntegral.lean:108).
   · -- map_mul: chosenRep (a * b) is continuously homotopic to (chosenRep a).concat (chosenRep b). Apply homotopyInvariance to switch to the concatenated analytic loop, then apply the concatenation theorem from step 4.
   ```

6. **(P4) Abelianize.** Because the target `HolomorphicOneForm X →ₗ[ℂ] ℂ` is a commutative additive group (i.e. `Multiplicative (… →ₗ[ℂ] ℂ)` is commutative), apply `Abelianization.lift` (Mathlib `GroupTheory.Abelianization`):
   ```
   Abelianization.lift loopIntegralOnFundGrp
     : Abelianization (FundamentalGroup X x₀) →* Multiplicative (HolomorphicOneForm X →ₗ[ℂ] ℂ)
   ```

7. **(P4) Switch to additive.** `H1 X x₀ = Additive (Abelianization (FundamentalGroup X x₀))` (`Homology.lean:41-42`). Compose with `Additive.toMul`/`AddMonoidHom.toMultiplicative` adapters; the result is the desired `AddMonoidHom`:
   ```
   noncomputable def loopIntegralToH1 (x₀ : X) :
       H1 X x₀ →+ (HolomorphicOneForm X →ₗ[ℂ] ℂ) :=
     (Abelianization.lift loopIntegralOnFundGrp).toAdditive.comp
       Additive.toMul.symm.toAddMonoidHom -- exact name pending API check
   ```

8. **(P5) Replace the axiom.** In `Jacobians/RiemannSurface/PathIntegral.lean`, replace `axiom loopIntegralToH1 …` (lines 101–104) with the `noncomputable def` built in step 7.

9. **(P6) Downstream cleanup.** No source edits should be needed in `Periods.lean` (it already routes through `loopIntegralToH1`, see `Periods.lean:42-43`); just confirm `#print axioms periodMap` no longer mentions `loopIntegralToH1`.

**Files touched**
- `Jacobians/RiemannSurface/PathIntegral.lean` — replace `axiom loopIntegralToH1` (lines 101–104) with a `noncomputable def`; add `pathIntegralAnalyticLoop`, ℂ-linearity lemma, concatenation/reversal lemmas, and the π₁ → Abelianization → Additive construction (steps 2, 4, 5, 6, 7).
- `Jacobians/RiemannSurface/AnalyticArc.lean` — promote the TODOs at lines 101–105 (concatenation, reversal) to real `def`s consumed by step 4.
- `Jacobians/RiemannSurface/Periods.lean` — no change to `periodMap`; verify the comment block at lines 10–15 ("Current status") still accurately describes the now-axiom-free situation.

**Acceptance**
- `lake build Jacobians.RiemannSurface.PathIntegral` succeeds.
- `lake build Jacobians.RiemannSurface.Periods` succeeds.
- `#print axioms Jacobians.RiemannSurface.periodMap` no longer lists `Jacobians.RiemannSurface.loopIntegralToH1` (it will list the prerequisite axioms `pathIntegralAnalyticArc`, `homotopyInvariance` until those are themselves discharged).
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; the real-axiom scanner count drops by 1.

**Risk / escalation triggers**
- The affine change-of-variables required in Step 4 interacting with `intervalIntegral_comp_mul_add` and chart coordinate mappings becomes intractable without missing 1D calculus lemmas.
- The fundamental-group-to-Abelianization descent requires a `Path.Homotopic.Quotient.lift`-style API that does not match the existing `Mathlib.Topology.Homotopy.FundamentalGroup` shape: pause for a human decision to ensure API compatibility.
- The statement signature of `loopIntegralToH1` needs to change (e.g. the H₁ encoding moves away from `Additive (Abelianization (FundamentalGroup X x₀))`, or the codomain switches from `→ₗ[ℂ] ℂ` to a different linear-functional flavor): escalate, since this affects every downstream consumer of `periodMap`.

## Gemini critique addressed:
- **Effort/Route Recalibrated:** Explicitly scoped the plan to `provable-from-other-axioms`, removing the Cauchy tiling topological arguments entirely and lowering effort from 9 to 4. 
- **Quotient/Choice Logic Fixed:** Step 5 is rewritten to use `chosenRep` mapping fundamental group elements to analytic representatives, completely bypassing `Quotient.lift` on continuous paths and correctly offloading the proof burden to `map_mul` via `homotopyInvariance`.
- **Change of Variables Noted:** Step 4 has been amended to explicitly call out the required affine change-of-variables (`intervalIntegral_comp_mul_add`) mapped through chart coordinate derivatives.
- **Topology Outsourced:** The missing infrastructure for Whitney approximation of continuous homotopies on manifolds has been moved entirely to a sub-plan.

## Sub-plans needed
- `homotopyInvariance` (`needs-infra`): A standalone infrastructure plan is needed to formally define the `homotopyInvariance` axiom, prove Cauchy-on-disks tiling for differential forms, and provide the massive Whitney approximation infrastructure necessary to relate purely continuous homotopies to piecewise-real-analytic ones.

---
**Vetting trail.** Critique: `_vetting/loopIntegralToH1.md`. Verdict: reject. Revised: 2026-06-03.

**Cross-plan patch (2026-06-03):** H1 type canonicalised to `Additive (Abelianization (FundamentalGroup X x₀))` so `Module ℤ` typeclasses elaborate.

**Cross-plan patch (2026-06-03):** Standardised manifold-model-space notation to `𝓘(ℂ, ℂ)` (Mathlib's `modelWithCornersSelf ℂ ℂ`); the single-arg alias `𝓘(ℂ)` caused typeclass-unification failures between generic and concrete plans.
