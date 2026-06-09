# Layer 3 — Phase C: the period cluster (Gemini-vetted design)

*2026-06-09. Faithful Layer-3 axiomatization for discharging the period cluster
(`AX_PeriodLattice`, `AX_RiemannBilinear`, `AX_AnalyticCycleBasis`,
`intersectionForm`+laws, `AX_H1FreeRank2g`), mirroring the Phase-B success.
Vetted by Gemini deep-think. Principle: **axiomatize basis-free functorial
properties; let matrices/bases/lattices be theorems.***

## The minimal faithful primitives (basis-free)
1. **`AX_H1_Unimodular`** (topology): `H₁(X;ℤ)` is free of rank `2g`, with a
   **unimodular alternating** intersection form `⟨·,·⟩ : H₁ × H₁ → ℤ`.
   *(≈ the existing `intersectionForm`/`_alternating`/`_perfect`; keep/repackage.)*
2. **`AX_PeriodMap`** (analysis): `Per : Ω¹(X) →ₗ[ℂ] Hom(H₁, ℂ)`, `ω ↦ (γ ↦ ∫_γ ω)`.
3. **`AX_RBR1`** (isotropy / Stokes): `⟨Per ω, Per η⟩* = 0` for all `ω, η ∈ Ω¹`,
   where `⟨·,·⟩*` is the intersection form transported to `Hom(H₁,ℂ)`.
   *(= `∫_X ω∧η = 0`, type (1,0)∧(1,0)=0 — but stated via the intersection form,
   which **bypasses 2-form integration in Lean**.)*
4. **`AX_RBR2`** (Hodge positivity): `i · ⟨Per ω, conj(Per ω)⟩* > 0` for `0 ≠ ω`.
   *(= `i∫_X ω∧ω̄ > 0`, again via the dual intersection form.)*
5. *(optional)* **`AX_SmoothRep`**: every `h ∈ H₁` has a piecewise-analytic loop
   representative — **only if** the Lean period integral rigidly needs analytic
   paths. **Preferred: drop it** — holomorphic forms are closed, so `∫_γ ω` is
   homotopy-invariant over any *continuous* loop (the analytic requirement is a
   textbook artifact, not a mathematical necessity).

## The reductions (theorems over the primitives)
Choose a symplectic basis `{A_i,B_i}` of `H₁` (from `AX_H1_Unimodular` + the
symplectic-basis lemma), and a dual `Ω¹`-basis `ω_j` with `∫_{A_i} ω_j = δ_ij`;
set `τ_ij = ∫_{B_i} ω_j`.
- **`THM_SymplecticBasis`** — symplectic ℤ-basis from the unimodular alternating
  form (pure linear algebra). Retires `AX_AnalyticCycleBasis`'s **algebraic** part.
  *(Gated on the ℤ integral-lattice-splitting lemma — Mathlib gap; field version
  done in #124. The analytic-rep part: drop, or `AX_SmoothRep`.)*
- **`THM_NormalizedDifferentials`** — the dual `ω_j` exist (RBR2 ⇒ no form has all
  zero A-periods).
- **`THM_Tau_Symmetric`** (`τ = τᵀ`) — from `AX_RBR1` expanded on `ω_i, ω_j`.
- **`THM_Tau_PosDef`** (`Im τ ≻ 0`) — from `AX_RBR2` on `ω = Σ c_j ω_j` ⇒
  `cᵀ (Im τ) c̄ > 0`. **Retires `AX_RiemannBilinear`.**
- **`THM_Lattice_Discrete_Rank2g`** — the `2g` columns of `(I | τ)` are
  ℝ-independent: `x + τy = 0` ⇒ `(Im τ) y = 0` ⇒ (pos-def) `y = 0` ⇒ `x = 0`;
  `2g` ℝ-independent vectors in `ℂ^g ≅ ℝ^{2g}` ⇒ discrete rank-`2g` lattice.
  **Retires `AX_PeriodLattice`.** *(Discreteness is a THEOREM — axiomatizing it
  would be unfaithful + overdetermined, since positivity forces it.)*

## Faithfulness traps (Gemini)
- **Never axiomatize `Im τ ≻ 0` / properties of `τ` directly** — that hard-codes a
  basis choice and makes the `Sp(2g,ℤ)` change-of-basis a nightmare. Axiomatize the
  basis-free RBR; `τ`'s properties are theorems *relative to a chosen basis*.
- **Don't axiomatize discreteness AND positivity** — overdetermined (positivity
  forces discreteness); a future model could violate the hidden dependency.
- The "dual intersection form on periods" framing is what keeps `AX_RBR1/2`
  faithful while avoiding 2-form integration.

## Irreducible content (stays axiomatized) vs. theorems
- **Axioms (irreducible analytic/topological reality):** `AX_H1_Unimodular`
  (integral Poincaré duality), `AX_PeriodMap` (the integral exists), `AX_RBR1`
  (Stokes), `AX_RBR2` (Hodge metric positivity).
- **Theorems:** the symplectic basis, `τ` symmetric + `Im τ ≻ 0` (`AX_RiemannBilinear`),
  the period lattice full-rank discreteness (`AX_PeriodLattice`), `H₁≅ℤ^{2g}`.

## Build order / gates
Primitives → `THM_NormalizedDifferentials` → `THM_Tau_Symmetric`/`THM_Tau_PosDef`
→ `THM_Lattice_Discrete_Rank2g`. `THM_SymplecticBasis` needs the ℤ-lattice-splitting
lemma (or its own clean axiom). Start after the Phase-B cohomology approach is
owner-endorsed (#126), and after deciding the `AX_SmoothRep`-vs-drop question by
inspecting what `loopIntegralToH1`/`periodMap` actually require.

Each primitive gets the full vetting protocol + `(NOT VERIFIED)` until cleared.
Vetting: Gemini deep-think 2026-06-09.
