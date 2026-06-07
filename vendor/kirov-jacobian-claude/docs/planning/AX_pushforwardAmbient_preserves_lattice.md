# `AX_pushforwardAmbient_preserves_lattice` — discharge recipe

**Location:** `Jacobians/Axioms/AbelJacobiMap.lean:310`
**Route:** needs-infra &nbsp;&nbsp; **Effort:** 8 &nbsp;&nbsp; **Est:** ~3–4 focused weeks, ~600–800 LOC (~60% shared with `AX_pullbackAmbient_preserves_lattice`)
**Blocked by:** `AX_AnalyticCycleBasis`, `AX_PeriodLattice`

**Statement (verbatim):**
```lean
/-- **Axiom.** Lattice preservation: the pushforward ambient map sends
the period lattice of `X` into the period lattice of `Y`.

Classical content: the period-map naturality `∫_{f_*γ} ω_Y = ∫_γ
(pullbackOneForm f) ω_Y`, combined with the fact that `f_*` sends
integer cycles to integer cycles. Retires to a theorem once
`pushforwardH1` + path-integral naturality land. -/
axiom AX_pushforwardAmbient_preserves_lattice {X : Type u}
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [ConnectedSpace Y] [Nonempty Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ, ℂ) ω Y] (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f) :
    ∀ v ∈ (periodLatticeInBasis X (Classical.arbitrary X)
              (jacobianBasis X)).toAddSubgroup,
      (pushforwardAmbientLinear f hf) v ∈
        (periodLatticeInBasis Y (Classical.arbitrary Y)
          (jacobianBasis Y)).toAddSubgroup
```

**Why it's an axiom right now:** The statement explicitly awaits two bounded infrastructure pieces: a genuine topological `pushforwardH1` and the analytic path-integral naturality lemma (change-of-variables formula). `pushforwardAmbientLinear` (`Jacobians/Axioms/AbelJacobiMap.lean:272–284`) is the dual of `pullbackOneForm f hf`; the period lattice (`Jacobians/Axioms/PeriodLattice.lean:60–68`) is the range of `periodMapInBasis` (`PeriodLattice.lean:57–58`). We need topological functoriality for $H_1$ to bridge the two cleanly. Mumford Vol I §III, Forster §20.

**Proof recipe**

1. **Construct `pushforwardH1` topologically.** Do not attempt basis-transport or circular period-map hacks. Build genuine topological functoriality for $H_1$. Create `Jacobians/Axioms/H1Functoriality.lean`. In Mathlib, the fundamental group of a space $X$ at $x$ is `x ⟶ x` in the `FundamentalGroupoid`. Functoriality is provided by `FundamentalGroupoid.map f`. The homology group $H_1(X)$ is its `Abelianization`. Define `pushforwardH1 : H1 X x₀ →ₗ[ℤ] H1 Y (f x₀)` by taking the induced continuous map on fundamental groups via `FundamentalGroupoid.map f` and applying `Abelianization.map`.

2. **Prove path-integral naturality (change-of-variables infra).** We require the analytic fact that $\int_{f_* \gamma} \omega = \int_\gamma f^* \omega$.
   - This must be a formal theorem in the project, e.g., `contour_integral_pushforward_naturality` in `Jacobians/RiemannSurface/PathIntegral.lean` (or wherever `AbelJacobiMap.lean:98`'s integration API points).
   - The proof requires unfolding the definition of the line integral and `pullbackOneForm` (`Jacobians/Axioms/AbelJacobiMap.lean:130–138`), reducing to the real calculus chain rule in charts. This is a crucial missing infrastructure deliverable.

3. **Handle basepoint independence for the period lattice.** The axiom relies on `Classical.arbitrary X` and `Classical.arbitrary Y`, introducing a basepoint mismatch between $f(x_0)$ and $y_0$.
   - Insert a change-of-basepoint isomorphism using a path $\eta$ between $f(x_0)$ and $y_0$.
   - Prove a lemma showing that integrating a closed form over a cycle conjugated by $\eta$ (i.e., $\eta^{-1} * \gamma * \eta$) yields the same value as integrating over $\gamma$, because the difference vanishes upon `Abelianization`.
   - Conclude that `periodLatticeInBasis Y (Classical.arbitrary Y) b_Y = periodLatticeInBasis Y (f x₀) b_Y` (analogous to basepoint independence in `Jacobians/Axioms/H1FreeRank2g.lean:38–45`). Add `periodLatticeInBasis_basepoint_independent` to `Jacobians/Axioms/PeriodLattice.lean`.

4. **Extract bases and state period-map naturality.** Cite `AX_AnalyticCycleBasis` (`Jacobians/Axioms/AnalyticCycleBasis.lean:257`) to extract bases `b_X` and `b_Y` (definition at `AnalyticCycleBasis.lean:230`). Formulate `periodMap_pushforward_naturality` in `PeriodLattice.lean`:
   ```lean
   theorem periodMap_pushforward_naturality
       (f : X → Y) (hf : ContMDiff … f) (γ : H1 X x₀) (ω : HolomorphicOneForm Y) :
     (periodMapInBasis Y x₀_Y b_Y) (pushforwardH1 f hf γ) =
       (pushforwardAmbientLinear f hf) ((periodMapInBasis X x₀ b_X) γ)
   ```
   Discharge this squarely using the `contour_integral_pushforward_naturality` theorem proved in Step 2.

5. **Conclude lattice preservation.** Use `PeriodLattice.lean:63–68`, which states `periodLatticeInBasis X x₀ b_X = LinearMap.range (periodMapInBasis X x₀ b_X)`. Let $v$ be in the lattice; write $v = \text{periodMapInBasis } X \ x_0 \ b_X(\gamma)$. Apply `periodMap_pushforward_naturality` to show $(f_*)v = \text{periodMapInBasis } Y \ y_0 \ b_Y(f_* \gamma)$, which lies in `LinearMap.range (periodMapInBasis Y y_0 b_Y)`.

6. **Replace the axiom.** Replace `axiom AX_pushforwardAmbient_preserves_lattice` at `Jacobians/Axioms/AbelJacobiMap.lean:310` with `theorem`. Use `Submodule.apply_mem_map` tactics combined with basepoint independence (Step 3). Note that the mirror argument for `AX_pullbackAmbient_preserves_lattice` (line 324) shares Steps 1–4.

**Files touched**
- `Jacobians/Axioms/H1Functoriality.lean` *(new file)* — Defines `pushforwardH1` topologically using `FundamentalGroupoid` and `Abelianization`.
- `Jacobians/RiemannSurface/PathIntegral.lean` (or relevant integral file) — Contains the analytic `contour_integral_pushforward_naturality` chart-level proof.
- `Jacobians/Axioms/PeriodLattice.lean` — `periodMap_pushforward_naturality` and `periodLatticeInBasis_basepoint_independent` lemmas.
- `Jacobians/Axioms/AbelJacobiMap.lean` — Replace `axiom AX_pushforwardAmbient_preserves_lattice` (line 310) with `theorem`.

**Acceptance**
- `lake build Jacobians.Axioms.AbelJacobiMap` succeeds.
- `#print axioms Jacobians.Axioms.pushforwardImpl` (`Jacobians/Axioms/AbelJacobiMap.lean:542`) no longer lists `AX_pushforwardAmbient_preserves_lattice`.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1.

**Risk / escalation triggers**
- The analytic chart-level proof of `contour_integral_pushforward_naturality` ($\int_{f \circ \gamma} \omega = \int_\gamma f^* \omega$) blocks on missing foundational definitions of real manifold line integration.
- The `Abelianization` Mathlib API has missing properties linking it algebraically to the geometric loops actually consumed by the integration API, preventing the proof of basepoint conjugation invariance.

### **Gemini critique addressed:**
- **Route & Effort updated:** Reclassified from `provable-from-other-axioms` to `needs-infra`, increasing effort to 8 to reflect the missing topological and analytic components.
- **Removed fatal circularity:** Entirely deleted the "pragmatic alternative" that improperly defined `pushforwardH1` using the period lattice maps we were trying to prove.
- **Rigorous `H1` topological definition:** Explicitly mandated defining `pushforwardH1` via Mathlib's `FundamentalGroupoid` and `Abelianization` API.
- **Analytic change-of-variables:** Added a dedicated infrastructure step for proving `contour_integral_pushforward_naturality` down to chart-level real calculus.
- **Basepoint independence via conjugation:** Addressed the $f(x_0)$ vs $y_0$ mismatch explicitly using cycle conjugation by a path and fundamental group abelianization.

---
**Vetting trail.** Critique: `_vetting/AX_pushforwardAmbient_preserves_lattice.md`. Verdict: reject. Revised: 2026-06-03.

**Cross-plan patch (2026-06-03):** Standardised manifold-model-space notation to `𝓘(ℂ, ℂ)` (Mathlib's `modelWithCornersSelf ℂ ℂ`); the single-arg alias `𝓘(ℂ)` caused typeclass-unification failures between generic and concrete plans.
