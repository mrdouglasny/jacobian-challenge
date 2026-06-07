# `AX_genus_eq_zero_iff_homeo` — discharge recipe

**Location:** `Jacobians/Axioms/Uniformization0.lean:55`
**Route:** split — `(⇒)` is `provable-from-other-axioms`; `(⇐)` is `needs-infra` &nbsp;&nbsp; **Effort:** 6 (for the discharge of `(⇒)`; the `(⇐)` half remains a raw axiom pending De Rham/Hodge) &nbsp;&nbsp; **Est:** ~2–3 focused weeks once `AX_RiemannRoch` and `AX_SerreDuality` have landed, ~300–400 LOC for the biholomorphism construction alone
**Blocked by:** `AX_RiemannRoch` (`Jacobians/Axioms/RiemannRoch.lean:59`), `AX_SerreDuality` (`Jacobians/Axioms/SerreDuality.lean:54`), plus the divisor / `H⁰` / `H¹` / `LineBundle.ofDivisor` / `canonicalDivisor` interface in `Jacobians/RiemannSurface/LineBundle.lean` (lines 51, 65, 85, 104, 123, 128). The `(⇐)` direction additionally requires De Rham cohomology / Hodge / Stokes on real 2-manifolds, none of which are present in this codebase or Mathlib at this pin.

**Statement (verbatim):**
```lean
axiom AX_genus_eq_zero_iff_homeo {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] :
    genus X = 0 ↔ Nonempty (X ≃ₜ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1))
```

**Why it's an axiom right now:** The docstring at `Jacobians/Axioms/Uniformization0.lean:19–33` flags three classical routes for the `(⇒)` direction (Riemann–Roch + Serre duality, harmonic / Dirichlet construction, or Hodge theory). The `(⇒)` direction collapses to a short concrete derivation through `ProjectiveLine.stereographic` once `AX_RiemannRoch` and `AX_SerreDuality` are usable. The `(⇐)` direction, contrary to the docstring's claim at `Uniformization0.lean:32–33` ("just pull back forms through the homeomorphism"), is **analytically deep**: `HolomorphicOneForm` is not a topological invariant, so a bare `≃ₜ` does not transport holomorphic 1-forms in either direction.

**Gemini critique addressed.** The previous version of this recipe treated `(⇐)` as easy and claimed step 1 could "promote a homeomorphism to a biholomorphism" via a generic "manifold transport lemma" and then cite `HolomorphicOneForm` covariance. This is **mathematically false**. There is no such promotion: complex conjugation `ℂP¹ → ℂP¹` is a homeomorphism (in fact a diffeomorphism) that is anti-holomorphic, not holomorphic, witnessing that homeomorphisms of Riemann surfaces are not biholomorphisms in general. Asserting that any homeomorphism `X ≃ₜ S²` can be upgraded to a biholomorphism `X ≃ ℂP¹` is logically equivalent to the Uniformization Theorem itself — i.e., it begs the question. Moreover, even if one transports `X`'s complex structure forward along the homeomorphism to define a new complex structure on `S²`, the resulting target is not the standard `ℂP¹`, so `HolomorphicOneForm_projectiveLine_eq_zero` no longer applies. The correct mathematical direction is the opposite of what the original recipe assumed: one **first constructs a biholomorphism `X ≃ ℂP¹` via RR + SD on a point divisor**, and the homeomorphism `X ≃ₜ S²` is a downstream consequence obtained by composing with `ProjectiveLine.stereographic`. This recipe is now rewritten to reflect that.

**Proof recipe**

This follows Forster §27 (*Lectures on Riemann Surfaces*) and Miranda Ch. IV §5 (*Algebraic Curves and Riemann Surfaces*). Both textbooks construct the **biholomorphism** as the load-bearing object; neither attempts to recover the analytic genus from a bare homeomorphism without invoking Hodge / De Rham machinery.

**Part A — Forward direction `(⇒)`: `genus X = 0 ⟹ Nonempty (X ≃ₜ S²)`.**

The strategy is: RR + SD on a single point divisor produces a degree-1 meromorphic function `f : X → ℂP¹`; that function is a biholomorphism; compose with stereographic projection to get the homeomorphism.

1. **Pick a base point and form `D := [P]`.** Choose `P : X`. `Nonempty X` follows from `ConnectedSpace X` (any connected space is nonempty in Mathlib's convention; use `Classical.choice` against `ConnectedSpace.toNonempty` or the project's `Nonempty` instance pattern). Form `D := Divisor.single P : Divisor X` via the divisor interface in `Jacobians/RiemannSurface/LineBundle.lean:51`, with `Divisor.deg X D = 1` from `Jacobians/RiemannSurface/LineBundle.lean:65`. (If `Divisor.single` does not yet exist, add it as a one-line helper; do not amend the divisor axiom signature.)

2. **Riemann–Roch at `D`.** Specialize `AX_RiemannRoch` (`Jacobians/Axioms/RiemannRoch.lean:59–66`) at `D` under the hypothesis `genus X = 0`:

   ```
   finrank H⁰(𝒪([P])) − finrank H¹(𝒪([P])) = deg D + 1 − g = 1 + 1 − 0 = 2.
   ```

3. **Kill `H¹` via Serre duality.** Apply `AX_SerreDuality` (`Jacobians/Axioms/SerreDuality.lean:54–59`) at `D := [P]`:

   ```
   H¹(𝒪([P])) ≃ₗ[ℂ] (H⁰(𝒪(K − [P])))*,
   ```

   where `K := canonicalDivisor X` (`Jacobians/RiemannSurface/LineBundle.lean:123`). In genus 0, `deg K = 2g − 2 = −2`, so `deg(K − [P]) = −3 < 0`. Any non-zero global section `s ∈ H⁰(𝒪(K − [P]))` would yield an effective divisor `div(s) + (K − [P]) ≥ 0` with non-negative degree, contradicting `deg < 0`. Hence `H⁰(𝒪(K − [P])) = 0`, so by Serre duality `H¹(𝒪([P])) = 0`, so `finrank H¹ = 0`. (Package the `deg < 0 ⟹ H⁰ = 0` step as a small helper `H0_eq_zero_of_deg_neg` in a new `Jacobians/RiemannSurface/Vanishing.lean`.)

4. **Extract a degree-1 meromorphic function.** From steps 2–3, `finrank H⁰(𝒪([P])) = 2`. Constants give a 1-dimensional subspace; any `s ∈ H⁰(𝒪([P]))` outside that subspace produces, by ratio with a non-zero constant, a non-constant meromorphic function `f : X → ℂP¹` with exactly one simple pole at `P` (Forster §27 Lemma, Miranda IV.5).

5. **Promote `f` to a biholomorphism `φ : X ≃ ℂP¹`.** A non-constant holomorphic map between compact connected Riemann surfaces is surjective and has a well-defined degree. A simple pole at `P` means the fiber over `∞ ∈ ℂP¹` is `{P}` with multiplicity 1, so `deg f = 1`, and degree-1 holomorphic maps between compact connected Riemann surfaces are biholomorphisms (open-mapping + injectivity from degree-1 fibers + compactness). This uses `AX_BranchLocus` machinery from `Jacobians/Axioms/BranchLocus.lean` (now a **theorem**, `BranchLocus.lean:202`, so this machinery is available, not axiom-backed). Output: `Nonempty (X ≃ ProjectiveLine)` at the *biholomorphic* level — the load-bearing analytic isomorphism. Forget structure down to `Nonempty (X ≃ₜ ProjectiveLine)`.

6. **Compose with stereographic projection.** Use `ProjectiveLine.stereographic : ProjectiveLine ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1` (`Jacobians/ProjectiveCurve/Line.lean:279–281`, built from Mathlib's `onePointEquivSphereOfFinrankEq` per the docstring at `Jacobians/ProjectiveCurve/Line.lean:271–275`) and compose with the `Homeomorph` from step 5 to produce the required `X ≃ₜ Metric.sphere …`. Wrap in `Nonempty`.

**Part B — Reverse direction `(⇐)`: `Nonempty (X ≃ₜ S²) ⟹ genus X = 0`.**

This direction **cannot be discharged from RR + SD alone**. `HolomorphicOneForm` (defined in `Jacobians/RiemannSurface/OneForm.lean:148`, with carrier set at `OneForm.lean:120`) is an analytic invariant, depending on the complex structure and not just the topology. A homeomorphism `h : X ≃ₜ S²` provides no data about the complex structure of `X` and thus no map between `HolomorphicOneForm X` and `HolomorphicOneForm ProjectiveLine`.

The mathematically correct discharge of `(⇐)` proceeds via:
- **De Rham:** any holomorphic 1-form `ω` is closed (`dω = 0` by type/dimension on a 1-dimensional complex manifold).
- **Topology of `S²`:** `H¹_dR(S²; ℝ) = 0`, so every closed 1-form is exact: `ω = df` for some smooth `f : X → ℂ`.
- **Compactness + maximum principle:** if `df = ω` is holomorphic then `f` is holomorphic, hence constant by compactness of `X`, hence `ω = 0`.

Each of these steps requires De Rham cohomology, Stokes' theorem on real 2-manifolds, and the maximum modulus principle on compact complex 1-manifolds — none of which are available in Mathlib at this pin or in this codebase. **This direction is therefore reclassified as `needs-infra` and must remain axiomatic until that infrastructure lands.**

**Recommended packaging (do this in `Uniformization0.lean`).**

Split the single biconditional axiom into:

- `theorem genus_zero_implies_homeo` — the `(⇒)` direction, discharged by Part A above (route `provable-from-other-axioms`, blockers `AX_RiemannRoch` + `AX_SerreDuality`).
- `axiom AX_homeo_sphere_implies_genus_zero` — the `(⇐)` direction, kept as a raw axiom (route `needs-infra`, awaiting future De Rham / Hodge work).
- A small `theorem AX_genus_eq_zero_iff_homeo` (now an `Iff`-glue theorem, not an axiom) that combines the two. Net axiom count is unchanged in the short term, but the load-bearing analytic content is exposed in the right place.

If splitting is not desired at this checkpoint, the recipe still requires `(⇐)` to remain axiomatic — do **not** attempt to discharge it via "homeomorphism transport of `HolomorphicOneForm`".

**Next discrete deliverable.** Land step 1 (point divisor + `Divisor.single` helper) and step 3's `H0_eq_zero_of_deg_neg` vanishing lemma. These are RR/SD-free and unblock the rest of Part A as soon as the two upstream axioms are usable.

**Files touched**
- `Jacobians/Axioms/Uniformization0.lean` — split the existing `axiom` at line 55 into `theorem genus_zero_implies_homeo` (proved via Part A) + `axiom AX_homeo_sphere_implies_genus_zero` + glue theorem `AX_genus_eq_zero_iff_homeo`. Update the file docstring to retract the false "just pull back forms" claim at lines 32–33.
- `Jacobians/RiemannSurface/LineBundle.lean` — add `Divisor.single : X → Divisor X` with `deg (Divisor.single P) = 1`, if not already present.
- `Jacobians/RiemannSurface/Vanishing.lean` (new) — `H0_eq_zero_of_deg_neg : Divisor.deg X D < 0 → H0 (LineBundle.ofDivisor D) = 0`.
- `Jacobians/ProjectiveCurve/Line.lean` — no change required; `stereographic` at line 279 is already in the right shape.
- Possibly `Jacobians/Axioms/BranchLocus.lean` — surface the "degree-1 holomorphic map ⟹ biholomorphism" packaging used in step 5.

**Acceptance**
- `lake build Jacobians.Axioms.Uniformization0` succeeds.
- `lake build Jacobians` succeeds (no downstream regression).
- `#print axioms genus_zero_implies_homeo` lists only `AX_RiemannRoch`, `AX_SerreDuality`, the divisor / `H⁰` / `H¹` / `LineBundle.ofDivisor` / `canonicalDivisor` stubs, and Mathlib's `propext` / `Classical.choice` / `Quot.sound` — and crucially does **not** list `AX_genus_eq_zero_iff_homeo`.
- `#print axioms AX_genus_eq_zero_iff_homeo` (now a theorem) lists `AX_homeo_sphere_implies_genus_zero` instead of itself.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS. Real-axiom delta: the iff axiom is retired but a new (mathematically honest) `AX_homeo_sphere_implies_genus_zero` is introduced, so the net count is unchanged in the short term. Subsequent discharge of `(⇐)` is a separate `needs-infra` ticket.

**Risk / escalation triggers**
- If `Divisor.single` (point divisor) or `H0_eq_zero_of_deg_neg` cannot be added without touching the divisor / `H⁰` / `H¹` axiom signatures in `Jacobians/RiemannSurface/LineBundle.lean` (lines 51, 65, 85, 104, 123, 128), pause and escalate.
- The "degree-1 holomorphic map between compact connected Riemann surfaces is a biholomorphism" step (step 5) routes through `AX_BranchLocus`, which is **now a theorem** (`BranchLocus.lean:202`) and therefore usable directly — the earlier "not yet usable / temporarily introduce a small intermediate axiom `AX_degree_one_iff_iso`" escape hatch is no longer needed. If that theorem's form turns out to be insufficient for this conclusion, strengthen it rather than fudging step 5.
- **Do not** attempt to discharge Part B by transporting `HolomorphicOneForm` through a bare `≃ₜ`. That is the mathematical error this revision corrects; if a contributor attempts it, escalate.

---
**Vetting trail.** Critique: `_vetting/AX_genus_eq_zero_iff_homeo.md`. Verdict: reject. Revised: 2026-06-03.

**Cross-plan patch (2026-06-03):** Standardised manifold-model-space notation to `𝓘(ℂ, ℂ)` (Mathlib's `modelWithCornersSelf ℂ ℂ`); the single-arg alias `𝓘(ℂ)` caused typeclass-unification failures between generic and concrete plans.
