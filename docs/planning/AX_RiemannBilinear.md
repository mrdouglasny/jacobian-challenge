# `AX_RiemannBilinear` — discharge recipe

**Location:** `Jacobians/Axioms/RiemannBilinear.lean:69`
**Route:** needs-infra (re-classified from ROADMAP's `mathlib-now [review]`; the load-bearing prerequisites — integration of `(1,1)`-forms on a complex `1`-manifold, the Hodge inner product on `H⁰(X, Ω¹)`, and Stokes pulled back to the `4g`-gon — are not in Mathlib v4.28 and must be built as project infrastructure. If the Hodge layer cannot be built atop Mathlib's `MeasureTheory.divergence_thm` without further classical content, this collapses to `genuine-textbook`.) &nbsp;&nbsp; **Effort:** 9 &nbsp;&nbsp; **Est:** ~6+ focused months across multiple sub-projects (form-integration infra, polygon Stokes, then the bilinear identity, then symmetry+positivity), ~2000–3500 LOC total
**Blocked by:** `AX_AnalyticCycleBasis`, `loopIntegralToH1` (used by `periodMap`), plus an unnamed Hodge-inner-product layer and a Stokes-on-Riemann-surfaces layer (neither yet exists as a project axiom)

**Statement (verbatim):**
```lean
/-- **Axiom (Riemann's bilinear relations).** There exists a symplectic
`H_1` basis, a normalized `H⁰(Ω¹)` basis, and a Siegel-upper-half-space
matrix `τ` such that:

1. The A-periods of `ω` against the `α`-cycles of the symplectic basis
   are the identity: `∫_{α_i} ω_j = δ_ij`.
2. The B-periods against the `β`-cycles are `τ`: `∫_{β_i} ω_j = τ[i,j]`.

Since `τ ∈ SiegelUpperHalfSpace (genus X)` by the type, it is
automatically symmetric and has positive-definite imaginary part —
the content of Riemann's second bilinear relation. -/
axiom AX_RiemannBilinear {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] (x₀ : X) :
    ∃ (b : AnalyticCycleBasis X x₀)
      (cω : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X))
      (τ : SiegelUpperHalfSpace (genus X)),
      -- α-normalization: A-periods form the identity.
      (∀ i j : Fin (genus X),
        periodMap X x₀ (b.isBasis (αEmbed i)) (cω j) = if i = j then 1 else 0) ∧
      -- τ is the B-period matrix.
      (∀ i j : Fin (genus X),
        τ.val i j = periodMap X x₀ (b.isBasis (βEmbed i)) (cω j))
```

**Why it's an axiom right now:** The file's own docstring (lines 23–32) flags three substantive prerequisites: (a) multi-chart, homotopy-invariant path integration (only partly available via `loopIntegralToH1` at `Jacobians/RiemannSurface/PathIntegral.lean:101`); (b) the Hodge inner product `⟨ω, η⟩ := (i/2) ∫_X ω ∧ η̄` on `H⁰(X, Ω¹)`; (c) integration-by-parts / Stokes on the universal-cover fundamental polygon of `X`. None of (b) or (c) currently exists as project infrastructure or in Mathlib v4.28 — `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable` at `Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean:267` is for flat Euclidean rectangles/boxes only. The whole package — Hodge norm positivity *plus* the polygon Stokes identity — must land before either α-normalization or the symmetry/positivity of `τ` can be derived, because both reductions depend on the *general* bilinear identity (see "Gemini critique addressed" below).

**Proof recipe**

Following Mumford, *Tata Lectures on Theta I* §II.2, Thm II.2.1 (the canonical reference cited in the file at line 45); Forster, *Lectures on Riemann Surfaces* Ch. IV §15 and §20.7 (the period matrix and the bilinear relations as a Stokes consequence on the polygon); Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §7 and Ch. 2 §2 (eq. (2.1), the bilinear identity); Birkenhake–Lange, *Complex Abelian Varieties* Ch. 1 §3 (Riemann relations as the polarization condition).

> **Gemini critique addressed:** The previous draft contained a logical cycle in which Step 3 ("invert the A-period matrix") invoked the Hodge norm vanishing for forms with zero A-periods, *but* that vanishing is itself a consequence of the general Riemann bilinear identity (Mumford II.2 eq. (4)), which the old draft only proved later in Step 4. We resolve this by deriving the **general bilinear identity for an arbitrary unnormalized basis first** (new Step 3), then using it to prove A-period non-degeneracy and invert (new Step 4), then specializing to the normalized basis for symmetry/positivity of `τ` (new Steps 5–6). No step now depends on a later step.

1. **Hodge inner product layer (sub-project, prerequisite).** Define
   `hodgeInner : HolomorphicOneForm X →ₗ[ℂ] HolomorphicOneForm X →ₗ[ℂ] ℂ` by
   `⟨ω, η⟩ := (i/2) ∫_X ω ∧ η̄`, where `∧` is the wedge of `(1,0)` and `(0,1)`
   forms and the integral is over `X` (orientation from the complex structure,
   automatic). Prove `hodgeInner` is a positive-definite Hermitian form on
   `HolomorphicOneForm X`. Forster Ch. IV §19 / Griffiths–Harris Ch. 0 §7.
   Required Mathlib pieces: differential forms on charted spaces (only partial
   in Mathlib v4.28), integration of top-degree forms on a `ChartedSpace ℂ`
   (absent), wedge product of analytic-chart forms (absent). This **also**
   requires the pullback of forms to a planar coordinate chart, which is the
   same primitive needed by Step 2. File as its own `needs-infra` axiom
   `AX_HodgeInnerProduct` if it grows large.

2. **Polygon Stokes / pullback layer (sub-project, prerequisite).** Build the
   primitive `Path.lineIntegral`-on-`X` cannot supply: pullback of a smooth
   `(p, q)`-form on `X` to the planar fundamental `4g`-gon `P ⊆ ℝ²` via the
   universal cover, plus a Stokes-type identity for the resulting smooth
   `2`-form on `P` with piecewise-smooth boundary `∂P`. Mathlib's
   `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable` at
   `Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean:267` covers axis-aligned
   boxes only — bridging it to the polygon with corner identifications is the
   real work. Output API: for any closed smooth `1`-forms `ω, η` on `X`,
   ```
   ∫_X ω ∧ η = Σ_i (A_i(ω) · B_i(η) − B_i(ω) · A_i(η)),
   ```
   where `A_i, B_i` are the α- and β-periods under any fixed
   `AnalyticCycleBasis`. Mumford II.2 Lemma (eq. (3)); Forster §20.7 (proof of
   Thm 20.4); Griffiths–Harris Ch. 2 eq. (2.1).

3. **General Riemann bilinear identity (the core lemma — derived first to
   break the cycle).** Take an *arbitrary* (unnormalized) `ℂ`-basis
   `cω' : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)`
   (Mathlib type at `Mathlib/LinearAlgebra/Basis/Defs.lean:88`, namespaced
   `Module.Basis` per `Mathlib/LinearAlgebra/Basis/Basic.lean:40`). Take any
   `b : AnalyticCycleBasis X x₀` (existence via Step 0 = step 2′ below). Apply
   the polygon-Stokes API from Step 2 to *every pair* of holomorphic forms,
   and to the pair `(ω, η̄)`. The two specializations give:
   - **(3a) Holomorphic-holomorphic:** for any `ω, η` holomorphic,
     `0 = ∫_X ω ∧ η = Σ_i (A_i(ω) B_i(η) − B_i(ω) A_i(η))`, because `ω ∧ η`
     is a `(2, 0)`-form on a complex `1`-manifold and hence identically zero.
   - **(3b) Holomorphic-antiholomorphic / Hodge norm formula:** for any
     `ω` holomorphic, `2 · hodgeInner ω ω = i · Σ_i (A_i(ω) · B_i(ω̄) − B_i(ω) · A_i(ω̄))
     = −2 i · Σ_i (B_i(ω) · A_i(ω) − A_i(ω) · B_i(ω))`-type formula (Mumford
     II.2 eq. (4); Griffiths–Harris eq. (2.4)). In particular, the right-hand
     side is real and depends only on `(A_i(ω), B_i(ω))_i`.

4. **α-normalization via A-period non-degeneracy (now justified by Step 3b,
   *not* by a forward reference).** Form the A-period matrix
   `A[i,j] := periodMap X x₀ (b.isBasis (αEmbed i)) (cω' j)` using `periodMap`
   from `Jacobians/RiemannSurface/Periods.lean:39`. Suppose `A · v = 0` for
   some `v ∈ ℂ^g`. Let `ω_v := Σ_j v_j (cω' j)`; then by linearity
   `A_i(ω_v) = 0` for all `i`. By **Step 3b**, `hodgeInner ω_v ω_v` is a sum
   of period products each of which has `A_i(ω_v) = 0` as a factor, so
   `hodgeInner ω_v ω_v = 0`. By positive-definiteness of `hodgeInner`
   (Step 1), `ω_v = 0`, and since `cω'` is a basis `v = 0`. Hence `A` is
   invertible. Define `cω j := Σ_k (A⁻¹)_{j,k} (cω' k)`; this gives the
   normalized basis with
   `periodMap X x₀ (b.isBasis (αEmbed i)) (cω j) = δ_{ij}`. This is the
   identity required by the first conjunct of the axiom.

5. **Symplectic A/B basis fixed by Step 0.** Apply `AX_AnalyticCycleBasis` at
   `Jacobians/Axioms/AnalyticCycleBasis.lean:257` to obtain
   `Nonempty (AnalyticCycleBasis X x₀)`; destruct to fix the
   `b : AnalyticCycleBasis X x₀` used uniformly across Steps 3–4 and below.
   The symplectic field at `Jacobians/Axioms/AnalyticCycleBasis.lean:238–242`
   gives `α_i · α_j = β_i · β_j = 0` and `α_i · β_j = δ_{ij}` under
   `intersectionForm`. The α- and β-embedding helpers are `αEmbed`
   (`AnalyticCycleBasis.lean:198`) and `βEmbed`
   (`AnalyticCycleBasis.lean:205`).

6. **Symmetry of `τ` (Riemann's first bilinear relation).** Apply **Step 3a**
   with `ω = cω i, η = cω j`. The A-periods are `δ_{ki}` and `δ_{kj}`
   respectively (Step 4 normalization), so the identity collapses to
   `0 = Σ_k (δ_{ki} · B_k(cω j) − B_k(cω i) · δ_{kj})
      = B_i(cω j) − B_j(cω i)
      = τ[i,j] − τ[j,i]`.
   Hence `τ.IsSymm` (Mathlib def `Matrix.IsSymm` at
   `Mathlib/LinearAlgebra/Matrix/Symmetric.lean:33`).

7. **Positivity of `Im τ` (Riemann's second bilinear relation).** Take any
   `0 ≠ v ∈ ℝ^g` and set `ω_v := Σ_j v_j (cω j)`. Then `A_k(ω_v) = v_k` and
   `B_k(ω_v) = Σ_j v_j τ[k,j]`. By **Step 3b**, `2 · hodgeInner ω_v ω_v` equals
   (up to the explicit Mumford-II.2-eq.(4) constants) `−2 · v^T · Im(τ) · v`,
   which is `> 0` by positivity of `hodgeInner` (Step 1) and `v ≠ 0`. So
   `Im(τ)` is positive-definite as a real matrix. (No `LinearMap.PosDef`
   declaration exists in Mathlib — we want `Matrix.PosDef` at
   `Mathlib/LinearAlgebra/Matrix/PosDef.lean:160` applied to
   `τ.val.map Complex.im`, exactly what `SiegelUpperHalfSpace.imPosDef` at
   `Jacobians/AbelianVariety/Siegel.lean:54` expects. For an alternative
   `QuadraticMap.PosDef` route, see
   `Mathlib/LinearAlgebra/QuadraticForm/Basic.lean:1138`, but `Matrix.PosDef`
   is the direct match for the Siegel constructor.)

8. **Package `τ : SiegelUpperHalfSpace (genus X)` and conclude.** Bundle the
   symmetry from Step 6 and the positivity from Step 7 through the
   constructor at `Jacobians/AbelianVariety/Siegel.lean:40` (`isSymm` at
   line 51, `imPosDef` at line 54). Bundle `b, cω, τ` and the two pointwise
   period identities: the first by construction (Step 4), the second by
   definition `τ[i,j] := B_i(cω j)`. Replace `axiom` with `theorem` in
   `Jacobians/Axioms/RiemannBilinear.lean:69`.

**Next discrete deliverable:** Build the **polygon Stokes / form-pullback
layer** (Step 2). This is now the *first* mathematical prerequisite for
every subsequent step (Steps 3, 4, 6, 7 all use the bilinear identity), so
it must land before the Hodge layer can even be tested end-to-end. A
self-contained deliverable: stand up `Jacobians/RiemannSurface/StokesPolygon.lean`
with (i) pullback of a `C^∞` chart-defined `1`-form on `X` along the universal
cover into a planar `4g`-gon `P ⊆ ℝ²`, (ii) Mathlib's
`MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable`
(`Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean:267`) extended from
boxes to a triangulated polygon, (iii) the corner-identification bookkeeping
that turns the eight boundary segments into the four telescoping pairs
`A_i B_i − B_i A_i`. Filing this as a fresh axiom `AX_PolygonStokes` (and
later `AX_HodgeInnerProduct` for Step 1) is acceptable; with both axioms in
hand, the present recipe collapses to a few hundred LOC of algebraic
manipulation in Steps 3–8.

**Files touched**
- `Jacobians/Axioms/RiemannBilinear.lean` — replace `axiom AX_RiemannBilinear`
  (line 69) with the `theorem`; remove the leading `axiom` keyword and add the
  proof term invoking the new helpers.
- `Jacobians/RiemannSurface/StokesPolygon.lean` *(new — Step 2)* — pullback +
  fundamental-polygon Stokes identity, bridging Mathlib's planar divergence
  theorem to the cut surface; outputs the general bilinear identity used in
  Step 3.
- `Jacobians/RiemannSurface/HodgeInner.lean` *(new — Step 1)* — define
  `hodgeInner`, prove Hermitian + positive-definite, expose the
  `hodgeInner ω ω = Σ_i (A_i B_i − …)` formula needed in Steps 4 and 7.
- `Jacobians/RiemannSurface/Periods.lean` — add helper lemmas
  (`periodMap_alpha_apply`, `periodMap_beta_apply`, linearity in the
  one-form) once `cω` and `b` are in scope; factor out the
  symmetry/positivity computations of Steps 6–7.

**Acceptance**
- `lake build Jacobians.Axioms.RiemannBilinear` succeeds (the narrowest module
  that consumes this axiom is the file itself; downstream consumers are
  `Jacobians/Axioms/PeriodLattice.lean`, `Jacobians/Axioms/IntersectionForm.lean`,
  and `Jacobians/Axioms/AbelJacobiMap.lean` per ROADMAP rows for
  `AX_PeriodLattice`, `intersectionForm`, `AX_ofCurve_inj` — the last now a **theorem** (2026-06-05)).
- `#print axioms Jacobians.Axioms.AX_PeriodLattice` no longer lists
  `AX_RiemannBilinear` (it is in `blocked_by` per ROADMAP line 202). New
  axioms `AX_HodgeInnerProduct` and `AX_PolygonStokes` may appear instead
  during the transition.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS;
  net axiom count drops by 1 (from 90 to 89) once the new sub-axioms are
  themselves discharged; in the interim the count may temporarily rise by 1
  or 2 as `AX_HodgeInnerProduct` / `AX_PolygonStokes` are filed, then drop
  back below the baseline as they are discharged.

**Risk / escalation triggers**
- If the polygon-Stokes bridge (Step 2) needs
  `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable`
  (`Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean:267`) extensions
  beyond box-shaped domains that aren't in current Mathlib (e.g. Lipschitz
  boundary with corner identifications, or extension to a triangulated
  polygon via a partition-of-unity argument), stop and escalate; the
  fundamental-polygon argument may need a different formalization route
  (e.g. via simplicial chains and the de Rham theorem). This now blocks
  *every* downstream step, not just symmetry/positivity.
- If the Hodge-inner-product layer (Step 1) requires changing
  `HolomorphicOneForm X` (signature drift on what counts as a holomorphic
  `1`-form, e.g. switching to `MDifferentiableForm` or a Mathlib
  `Differentiable` form bundle that doesn't yet exist), stop and escalate —
  this would propagate to every downstream axiom and is not a local fix.
- If by Step 4 the A-period matrix `A` still cannot be shown invertible after
  the full Step 3b machinery is in place (e.g. a non-vanishing-of-periods
  lemma that is itself classical-textbook turns out to be required), escalate
  — splitting that out as a separate axiom `AX_APeriodMatrixInvertible` is a
  reasonable fallback, but the human should ratify the new statement.

---
**Vetting trail.** Critique: `_vetting/AX_RiemannBilinear.md`. Verdict: revise. Revised: 2026-06-03.

**Cross-plan patch (2026-06-03):** Standardised manifold-model-space notation to `𝓘(ℂ, ℂ)` (Mathlib's `modelWithCornersSelf ℂ ℂ`); the single-arg alias `𝓘(ℂ)` caused typeclass-unification failures between generic and concrete plans.
