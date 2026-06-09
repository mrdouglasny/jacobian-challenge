# Layer 3 — Phase C build plan (concrete, grounded in the merged engines)

*2026-06-09. Translates `LAYER3_PHASE_C_PERIODS.md` (the Gemini-vetted design)
into the specific Lean steps, using the actual interfaces of the merged engines
(#128 `PeriodLattice.lean`, #129 `RiemannBilinear.lean`) and the real discharge
targets. Goal: discharge the period/Hodge cluster by reducing it to two
basis-free primitives `AX_RBR1`, `AX_RBR2` over the existing period map.*

## What already exists (no new work)

**Matrix engine (axiom-free, merged):**
- `Layer3.PeriodLattice`: for a concrete `τ : Matrix (Fin g) (Fin g) ℂ`,
  `(τ.map Complex.im).PosDef → IsZLattice ℝ (periodLattice τ _)`; also
  `periodLinearMap_injective`, `periodColumns_linearIndependent`,
  `periodBasis`, and `periodLattice.discreteTopology`.
- `Layer3.RiemannBilinear`: `Q` (symplectic dual form on `PeriodVector g =
  ComplexVec g × ComplexVec g`), `col`/`omegaCol`/`conjCol`, and
  - `tau_symmetric_of_rbr1 : (∀ i j, Q (col τ i) (col τ j) = 0) → τ.IsSymm`
  - `tau_posDef_of_rbr2 : RBR1 → RBR2 → (τ.map Complex.im).PosDef`
  - `riemannBilinear_isZLattice : RBR1 → RBR2 → IsZLattice ℝ (periodLattice τ _)`

**Geometric infra (existing):**
- `RiemannSurface.periodMap X x₀ : H1 X x₀ →+ (HolomorphicOneForm X →ₗ[ℂ] ℂ)`
  — the period pairing `γ ↦ (ω ↦ ∫_γ ω)` (real `def` via `loopIntegralToH1`).
- `AX_AnalyticCycleBasis X x₀ : Nonempty (AnalyticCycleBasis X x₀)` — a symplectic
  ℤ-basis `{A_i, B_i}` of `H1 X x₀` with intersection numbers realising the
  standard symplectic form; subsumes `H1FreeRank2g`.
- `intersectionForm` + `_alternating`/`_perfect` — the `H1 × H1 → ℤ` pairing.

**Discharge targets (the period cluster, currently axioms):**
- `AX_PeriodLattice X x₀ b : IsZLattice ℝ (periodLatticeInBasis X x₀ b)` where
  `periodLatticeInBasis = LinearMap.range (periodMapInBasis X x₀ b)`,
  `b : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)`.
- `instPeriodLatticeDiscrete` — `DiscreteTopology (periodLatticeInBasis …)`
  (follows from `IsZLattice`, so it collapses once `AX_PeriodLattice` is a
  theorem).
- `AX_RiemannBilinear` — **existential** (this is the actual axiom shape): there
  exist a symplectic `H₁` basis `b : AnalyticCycleBasis X x₀`, a **normalized**
  form basis `cω : Basis (Fin g) ℂ (HolomorphicOneForm X)` with A-periods the
  identity (`periodMap x₀ (b.isBasis (αEmbed i)) (cω j) = δᵢⱼ`), and a
  `τ : SiegelUpperHalfSpace (genus X)` with B-periods `τ`
  (`τ.val i j = periodMap x₀ (b.isBasis (βEmbed i)) (cω j)`). The `Siegel` type
  **bakes in** `τ` symmetric + `Im τ ≻ 0`. *(Note: "symmetric in an **arbitrary**
  form-basis" is the known-**false** formulation; symmetry holds only for the
  **normalized** basis. We discharge this existential, not the arbitrary-basis
  claim — which is exactly what the reduction below produces.)*

## The two new primitives (to be vetted before committing)

Stated basis-free over `periodMap`, using the symplectic basis to read off the
A/B period vectors. The `AnalyticCycleBasis` API exposes the symplectic cycles as
`b.isBasis (αEmbed i)` (A-cycles) and `b.isBasis (βEmbed i)` (B-cycles) — there
are **no** `b.A`/`b.B` fields. For `ω : HolomorphicOneForm X` let
`periodVec b ω := (fun i => periodMap X x₀ (b.isBasis (αEmbed i)) ω,
                   fun i => periodMap X x₀ (b.isBasis (βEmbed i)) ω) : PeriodVector g`
(A-periods and B-periods of `ω` over the symplectic basis `b`). This matches the
period convention already used by `AX_RiemannBilinear`.

- **`AX_RBR1` (isotropy / Stokes).** For all `ω η : HolomorphicOneForm X`,
  `Q (periodVec b ω) (periodVec b η) = 0`.
  *Math:* `Q` over the symplectic basis = the cup-product / intersection
  pairing of the two closed `(1,0)`-forms `= ∫_X ω ∧ η = 0` since
  `(1,0)∧(1,0) = 0`. Stated via `Q` to **avoid 2-form integration** in Lean.
- **`AX_RBR2` (Hodge positivity).** For all `0 ≠ ω : HolomorphicOneForm X`,
  `0 < (Complex.I * Q (periodVec b ω) (conjPeriodVec b ω)).re`
  where `conjPeriodVec b ω := (star A-periods, star B-periods)`.
  *Math:* `= i ∫_X ω ∧ ω̄ > 0`, the Hodge metric positivity on holomorphic
  1-forms; again routed through `Q` to avoid 2-form integration.

Both are independent of the *form* basis (quantified over all `ω`) but use the
chosen symplectic *homology* basis `b` (legitimate: a different symplectic basis
is an `Sp(2g,ℤ)` change preserving `Q`). They are the genuine Stokes / Hodge
inputs — the irreducible analytic reality.

### Statement vetting (2026-06-09, `DT`, statement-first — verdict SATISFIABLE/FAITHFUL)
Both proposed statements were vetted per-axiom by Gemini deep-think **before any
Lean commitment**:
- **`AX_RBR1`**: confirmed = the first Riemann bilinear relation. `Q(periods) =
  ∫_X ω∧η = 0` because `(1,0)∧(1,0)=0` on a curve; the `=0` conclusion is
  sign-convention-independent. Forces `τ` symmetric (the period subspace is
  Lagrangian for `Q`, not all-zero). Non-vacuous, well-typed.
- **`AX_RBR2`**: confirmed = the second Riemann bilinear relation, **sign
  verified** on the genus-1 torus `ℂ/(ℤ+τℤ)`: with `ω=dz`, `A`-period `1`,
  `B`-period `τ`, `Q(v,v̄)=1·τ̄−τ·1=−2i·Im τ`, so `(i·Q).re = 2·Im τ > 0` ⟺
  `Im τ > 0` — exactly the proposed inequality with the proposed `Q`-ordering and
  `conjPeriodVec`. `i·Q` is purely real (`Q` is purely imaginary since each term
  is `z−z̄`), so `.re` is lossless. Forces `Im τ ≻ 0` (the `c* (Im τ) c` form).
  *This is the classic sign-trap location; the proposed sign is correct.*

Cleared to commit both as `Periods.lean` primitives `(NOT VERIFIED)`.

## Reduction steps (theorems over the primitives)

1. **`THM_NormalizedDifferentials`** (axiom-free given RBR2). The A-period matrix
   `Aᵢⱼ = periodMap x₀ (b.isBasis (αEmbed i)) ωⱼ` (for a fixed form-basis `cω`)
   is invertible:
   if some `0 ≠ c` had `A c = 0`, the form `ω = Σ cⱼ ωⱼ` would have all
   A-periods zero, contradicting `AX_RBR2` (positivity ⇒ no nonzero form has
   vanishing A-periods). Normalize `ω̂ = b · A⁻¹` so that
   `periodMap x₀ (b.isBasis (αEmbed i)) ω̂ⱼ = δᵢⱼ`. Then
   `τᵢⱼ := periodMap x₀ (b.isBasis (βEmbed i)) ω̂ⱼ`.
2. **`THM_Tau_Symmetric`** — `τ.IsSymm`, from `AX_RBR1` on `ω̂ᵢ, ω̂ⱼ` via
   `tau_symmetric_of_rbr1` (the normalized period vector of `ω̂ⱼ` is exactly
   `col τ j = (Pi.single j 1, τ ·ⱼ)`).
3. **`THM_Tau_PosDef`** — `(τ.map Complex.im).PosDef`, from `AX_RBR1`+`AX_RBR2`
   via `tau_posDef_of_rbr2` (`omegaCol τ c` is the normalized period vector of
   `Σ cⱼ ω̂ⱼ`). **Discharges `AX_RiemannBilinear`.**
4. **`THM_Lattice`** — `IsZLattice ℝ (periodLattice τ _)` via the engine; then
   identify `periodLatticeInBasis X x₀ b` with `periodLattice τ` up to the
   ℂ-linear change of form-basis `b ↦ ω̂` (an element of `GL_g(ℂ)`, which is an
   `ℝ`-linear automorphism of `ℂ^g` preserving full-rank-ness and discreteness).
   **Discharges `AX_PeriodLattice` and `instPeriodLatticeDiscrete`.**

## Net axiom effect
+2 (`AX_RBR1`, `AX_RBR2`) − 3 (`AX_RiemannBilinear`, `AX_PeriodLattice`,
`instPeriodLatticeDiscrete`) = **−1**, and a faithfulness gain: the period
cluster becomes theorems over the genuine Stokes + Hodge-positivity inputs,
which are one step closer to a Mathlib 2-form-integration discharge.

## Gates / risks
- The change-of-basis identification in step 4 (`periodLatticeInBasis b ≅
  periodLattice τ`) is real linear algebra over `Fin g → ℂ`; needs the
  `periodMapInBasis` definition unfolded and a `GL_g(ℂ)`-transport lemma.
- `THM_NormalizedDifferentials` needs `Matrix.nonsing_inv` over the invertible
  A-period matrix; the invertibility proof uses `AX_RBR2` contrapositively.
- The symplectic-basis *algebraic* part (`THM_SymplecticBasis`, retiring the
  algebraic content of `AX_AnalyticCycleBasis`) is **out of scope here** — it
  needs the ℤ integral-lattice-splitting lemma (Mathlib gap; field version in
  #124). Phase C uses the symplectic basis as supplied by `AX_AnalyticCycleBasis`.

## Build order
Vet `AX_RBR1`/`AX_RBR2` statements (per-axiom) → `Periods.lean` with the 2
primitives `(NOT VERIFIED)` → steps 1–4 as theorems → wire discharges →
`#print axioms` + guard. Each primitive carries `(NOT VERIFIED)` until cleared.
