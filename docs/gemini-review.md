# Gemini 3 Pro Review of the Formalization Plan

Received 2026-04-20 via `mcp__gemini__chat_gemini` (model `gemini-3-pro-preview`). I asked for adversarial, non-rubber-stamp pushback on 14 specific questions. Review is reproduced verbatim below, followed by our triage.

---

## Gemini's verdict on each point

### 1. `Jacobian X := AbelianVariety (τ X)` — "Definitional Catastrophe"

**Claim.** `τ(X)` needs a symplectic basis of `H_1(X, ℤ)`. If hidden by `Classical.choice`, the type `Jacobian X` is defined relative to an arbitrary unnameable basis; then `pushforward : Jacobian X →ₜ+ Jacobian Y` has to transport between arbitrary bases on both sides, pushing the project into non-computable equivalence-class hell.

**Fix.** Define the Jacobian basis-free: use `(H⁰(X, Ω¹))^∨` as the ambient ℂ-vector space, the image of `H_1(X, ℤ)` under the period pairing as `Λ`. Siegel period matrix is a *theorem about Λ*, not the definitional foundation.

### 2. Chart-cocycle `HolomorphicOneForm` vs cotangent bundle

**Claim.** Don't use chart-cocycles; Mathlib 4 resists coordinate-based definitions. Every integral evaluation destructs a quotient, sums over a partition of unity, proves coordinate independence.

**Fix.** Mathlib already has `CotangentBundle` / vector-bundle API. A holomorphic 1-form is a `ContMDiff` (holomorphic) ℂ-linear map from the tangent space to ℂ. Use Mathlib's vector-bundle API rather than reinvent.

### 3. Dependent types — `ChartedSpace (Fin (genus X) → ℂ) (Jacobian X)`

**Claim.** `genus X := Module.finrank ℂ (HolomorphicOneForm X)` is fine mathematically, but `Fin (finrank V) → ℂ` is a rigid type; proving `Jacobian X ≃ (Fin (genus X) → ℂ)` as a charted-space isomorphism pushes a non-canonical basis choice into typeclass inference, which will fail.

**Fix.** You will need an explicitly chosen (non-canonical) isomorphism `(H⁰(X, Ω¹))^∨ ≃ ℂ^g`, bundled into the `ChartedSpace` structure. Unavoidable abrasion given Buzzard's signature.

### 4. `𝓘(ℂ)` vs `modelWithCornersSelf ℂ (Fin g → ℂ)`

**Claim.** These are *not* definitionally equal for `g = 1`. Buzzard's file mixing them is a latent trap: `X` modeled on `𝓘(ℂ)`, `Jacobian X` on `modelWithCornersSelf`; lemmas like `ofCurve_contMDiff` will need explicit structural casts.

### 5 & 6. `LieAddGroup` smoothness + Rothgang's PR

**Claim.** Don't wait for Rothgang, don't write generic discrete-group quotient. `ℂ^g / Λ ≃ (ℝ/ℤ)^{2g}` as real Lie groups. Mathlib already has `AddCircle = ℝ/ℤ` as a Lie group; transport the structure. Generic covering-map infrastructure is a 2000-line yak shave we don't need.

*(Caveat I'd add: the transport gives the real-Lie-group structure, but the complex structure requires additional care since the real diffeomorphism is not automatically holomorphic. Still, it's a big shortcut.)*

### 7. `AX_AbelTheorem` — too heavy? Forster-style residue proof?

**Claim.** "Residue calculus" is not in Mathlib for manifolds. Forster Ch. III relies on meromorphic functions, winding numbers around branch points, Stokes on domains with holes — Mathlib barely has Cauchy's integral formula for the plane. Can't discharge sooner.

**Refinement.** For `ofCurve_inj` (Abel for 1 point: `∫_P^Q ω ≡ 0 ⇒ P = Q`), use a holomorphic 1-form with a pole at `P, Q`. Still requires axiomatic framework for meromorphic differentials.

### 8. `AX_Uniformization0` — Riemann-Roch-free?

**Claim.** RR-free proof requires full Uniformization (Beltrami / Dirichlet). That is *harder*, not easier, than RR.

**Fix.** Use algebraic geometry: genus 0 ⇒ (via RR) there's a meromorphic function with exactly one simple pole ⇒ biholomorphism to ℙ¹. So the correct axiom is `AX_RiemannRoch`, and from it `AX_Uniformization0` is derivable.

### 9. `ofCurve_self` type-checking

**Agreement.** `ofCurve P Q := [∫_P^Q ω]` in `ℂ^g / Λ`. The constant path has zero integral, and `π(0) = 0`. The hard part is proving "integral over constant path = 0" in our path-integral framework.

### 10. `pushforward_pullback = deg • id` — 2 weeks?

**Claim.** 2 weeks is ridiculous; try 6 months. Need: (i) branch locus of a holomorphic map between compact Riemann surfaces, (ii) prove it's finite, (iii) define integration along fibers of a branched cover, (iv) prove pulled-back form integrated along fiber = degree · form. Mathlib has none of this.

### 11. Hyperelliptic `√f` branch choice on α/β cycles

**Claim.** The 2-sheet atlas does *not* handle it automatically. Constructing explicit loops requires defining line segments between roots in ℂ, lifting to the surface, proving non-intersection at endpoints. `Complex.cpow` branch-cut handling in Lean is painful (branch cuts are half-open, limits across are not definitionally equal). This absolutely bleeds into the proof.

### 12. Time budget realism

**Claim.** Utterly unrealistic. Bochner integration took multiple man-years. Integration of 1-forms along smooth paths mod homotopy is monumental — Stokes for singular 2-simplices, homotopy invariance, etc. `PathIntegral` alone: expect 3 months of dedicated Lean work, not 3–6 weeks.

### 13. Constructions missed

- **Intersection pairing on `π₁^{ab}`** — needed for symplectic basis and Riemann bilinear relations.
- **Hurewicz homomorphism** — from smooth loops to `H_1`.
- **Injectivity of `H_1(X, ℤ) → H⁰(X, Ω¹)^∨`** via periods — a separate step our plan didn't call out.

### 14. Mathlib idioms — `IsZLattice`

**Claim.** Use Mathlib's `IsZLattice` (or `ZLattice`), which gives discreteness, fundamental domains, quotient topology essentially for free (it already hooks `DiscreteTopology`, which makes quotients of Hausdorff groups Hausdorff). Writing our own `FullRankLattice` is duplicative and forces us to re-prove these.

### Summary

"Your Bridge is structurally flawed due to basis-dependence; your Part B relies on coordinate cocycles which are an anti-pattern in Lean 4 geometry. Discard the Siegel matrix as the definitional basis of the Jacobian, use Mathlib's `CotangentBundle` and `IsZLattice`, and prepare for the path-integral to take twice as long as your entire proposed budget."

---

## Our triage

| # | Gemini's point | Verdict | Action |
|---|---------------|---------|--------|
| 1 | Basis-dependence catastrophe | **Valid & serious** | Amend §5.1: `Jacobian X := (HolomorphicOneForm X →ₗ[ℂ] ℂ) ⧸ periodImage`. Siegel matrix is a *theorem about* `Jacobian X`, not the definition. |
| 2 | Chart-cocycle is anti-pattern | **Valid but needs Mathlib check** | Before committing, survey Mathlib's `CotangentBundle` / `VectorBundle`. If usable for complex manifolds, switch. Else chart-cocycle with explicit note. |
| 3 | `Fin (genus X) → ℂ` dep-type pain | **Valid, unavoidable** | §5.1: use `Basis.equivFun` for the forced basis; document as structural cast. |
| 4 | `𝓘(ℂ)` ≠ `modelWithCornersSelf ℂ (Fin g → ℂ)` | **Valid** | §5.1: add explicit `IsManifold.congr` / `ChartedSpace.congr` casts; flag as one of the fiddly but unavoidable typeclass gymnastics. |
| 5+6 | Transport from `(AddCircle)^{2g}` | **Valid shortcut, partial** | §3.3: reframe. Real Lie-group structure via `AddCircle` transport. Complex-manifold structure still needs extra justification (real diffeo ≠ holomorphic). But the transport shortcut cuts the covering-map yak shave significantly. |
| 7 | `AX_AbelTheorem` stays | **Agree** | Keep axiomatized as planned. |
| 8 | `AX_Uniformization0` via `AX_RiemannRoch` | **Valid reframing** | Rename: replace `AX_Uniformization0` with `AX_RiemannRoch`, then derive genus-0 ⇒ ℙ¹ as a theorem. RR itself is still axiom-level for us. |
| 9 | `ofCurve_self` details | **Agreement** | No change; already captured. |
| 10 | Pushforward-pullback time: 6 months | **Partial** | Plan says 2 weeks assuming infrastructure is in place. Gemini's 6 months includes the infrastructure. Revise budget to 2 months once `HolomorphicOneForm`, `pathIntegral`, branch-locus theory are done. Total timeline from scratch is much longer. |
| 11 | Hyperelliptic branch cuts bleed | **Valid, downgrade Track 2 estimate** | §3.5.3: bump Hyperelliptic from 4 weeks to 8–10 weeks. Note `Complex.cpow` branch-cut pain as first-class risk. |
| 12 | Time budget unrealistic | **Valid** | Revise across the board: `PathIntegral` 3+ months, `RiemannTheta` 4–6 weeks (not 2), total Track 1 closed-modulo-axioms 9–12 months (not 5). Add "full autonomy" multiplier as separate column. |
| 13 | Intersection pairing, Hurewicz, `H_1 → (H⁰)^∨` injectivity | **Missed, real gaps** | New §4.6 `RiemannSurface/IntersectionForm.lean`. Hurewicz is available in Mathlib (`Abelianization` of `FundamentalGroup`); explicit call-out in §4.3. Injectivity of period map is `AX_PeriodInjective` and appears in §4.4. |
| 14 | `IsZLattice` | **Valid, verify in Mathlib at pin** | §3.1: replace `FullRankLattice` with Mathlib's `IsZLattice ℝ V` (if present at our pinned commit). If not, our definition is fine as a forward-port. Survey needed. |

## Net plan changes to make

1. **Rewrite §5.1** (Jacobian/Construction.lean) with basis-free definition. Period matrix `τ(X)` becomes a theorem statement, not a definitional input.
2. **Rewrite §4.1** (HolomorphicOneForm) to first check Mathlib `CotangentBundle` / `VectorBundle` support at the pinned commit before committing to the chart-cocycle approach. Preserve chart-cocycle as a fallback.
3. **Add §4.6** (IntersectionForm.lean, with Hurewicz + injectivity of `H_1 → (H⁰(Ω¹))^∨`).
4. **Amend §7 axioms**: `AX_Uniformization0` → `AX_RiemannRoch` + the uniformization step becomes a *derived* result.
5. **Rewrite §9 budget** with realistic numbers (PathIntegral 3 months, RiemannTheta 4-6 weeks, Hyperelliptic 8-10 weeks, Total ~9–12 months to closed-modulo-axioms).
6. **Rewrite §3.1** to use `IsZLattice` if available, else note the plan to upstream.
7. **Add §11 risk**: `Complex.cpow` branch cuts in hyperelliptic period integrals.
8. **Reframe §3.3** Lie-group instance via `AddCircle` transport, not covering maps.

These changes reduce architectural risk (points 1, 2, 4, 6, 8) and realign expectations (points 5, 7). Plan length will stay comparable; more honest.
