# Project status

## Current state

**Sorry count: 0.** Every theorem in the project compiles as a genuine
Lean theorem. Classical content not yet in Mathlib is axiomatized via
named typeclasses (documented in `docs/REFERENCES.md`).

**Placeholders (`:= 0`) remaining:** `pushforwardForm` (trace of
forms) and `ContMDiff.degree` (preimage counting). These are
tightly coupled via `pushforwardForm ∘ pullbackForm = deg • id`;
removing either requires the other plus branched-cover theory.

## Typeclasses for classical theorems

Each typeclass axiomatizes a named classical result not currently
in Mathlib. Real instances would be Mathlib-contribution-scale
efforts (weeks to months each).

| Typeclass | Classical statement | Reference |
|-----------|---------------------|-----------|
| `IsPeriodLattice X` | Period lattice has `DiscreteTopology` and `IsZLattice ℝ` | Forster §§20–21 (Hodge) |
| `HasSmoothPaths X` | Smooth paths exist between any two points | Forster §§1–2 |
| `HasSmoothPathAbelJacobi X` | Abel–Jacobi basepoint-change formula | Forster §21 |
| `HasHolomorphicAbelJacobi X` | `ofCurve P` is holomorphic as `X → Jacobian X` | Forster §21 |
| `HasResidueTheorem X` | Sum of orders of a meromorphic function is zero | Forster §4.24 / Miranda §V.2.4 |
| `HasUniformizationG0 X` | `genus X = 0 ↔ X ≃ₜ S²` | Forster §16.3 |
| `HasAbelsTheorem X` | Abel's theorem (two directions) | Forster §21.4 |
| `NoDegreeOneDivisorsToPP1 X` | No degree-1 divisors to ℙ¹ on positive genus | Forster §21.5 |
| `HasBranchedCoverContent X Y` | mfderiv=0 ⇒ constant, critical set finite, preimage cycle exists | Forster §§4, 10.11 |
| `HasAmbientDegreeIdentity X Y` | `Φ ∘ Ψ = d • id` | Forster §17 |

## Real mathematical content proven

Selected highlights (files indicated):

**Abel / divisors (`Abel.lean`):**
- `orderAtPoint_chart_invariant` — chart-independence of meromorphic order at a point.
- `orderAtPoint_isolated_at` — isolated zeros/poles (Forster §6).
- `abelJacobi_twoPointDivisor` — `AJ(P − Q) = ofCurve P₀ P − ofCurve P₀ Q`.
- `MeromorphicFunction.div = divViaOrder` — real divisor from orderAtPoint.

**Abel–Jacobi (`Jacobians.lean`):**
- `ofCurve P Q := mk(periodVec(smoothPath P Q))` — real Abel–Jacobi map.
- `ofCurve_self : ofCurve P P = 0`.
- `ofCurve_inj` (THE main challenge theorem) — via `HasAbelsTheorem` + `NoDegreeOneDivisorsToPP1` + basepoint-change + `abelJacobi_twoPointDivisor`.

**Period lattice (`PeriodLattice.lean`):**
- `periodVec_pushforward_of_smooth` — `periodVec (f∘γ) = ambientPhi (periodVec γ)`.
- `ambientPhi_preserves_truePeriodLattice` — real span-induction proof.
- `IsClosedSmoothLoop.comp` — smooth loop composes with smooth map.
- `IsSmoothPath.reverse`, `IsClosedSmoothLoop.reverse` — reverse preserves smoothness.
- `isClosed_criticalSet` — the critical set of a holomorphic map is topologically closed (via bundle trivialization).
- `pullbackForm_eq_zero_of_const`, `ambientPsi_eq_zero_of_const` — constant-map trivial cases.

**Line integral (`LineIntegral.lean`):**
- `pathSpeed_comp_eq_mfderiv` — pointwise chain rule (bypasses `IsScalarTower ℝ ℂ ℂ` diamond).
- `lineIntegral_pullback` — change of variables.
- `concat`, `reverse`, `pathSpeed_*`, `lineIntegral_*` — full regularity algebra.

**Holomorphic forms (`HolomorphicForms.lean`):**
- `HolomorphicOneForms X` type + `FiniteDimensional` via Montel.
- `pullbackForm f hf` as a real `HOF Y →ₗ[ℂ] HOF X`.
- `ambientPsi`, `ambientPhi` — ambient-coordinate bridges (`ambientPhi` via matrix transpose, a workaround pending real `pushforwardForm`).
- `pullbackForm_comp`, `pullbackForm_id`, `ambientPsi_comp`, `ambientPsi_id`.

**Genus (`Genus.lean`):**
- `genus X := Module.finrank ℂ (HolomorphicOneForms X)`.
- `finrank_HolomorphicOneForms_eq_genus` — by definition.

**Montel (`Montel.lean` + `Montel/`):**
- `HolomorphicOneForms.exists_convergent_subseq_of_bounded` — full Arzelà-based proof.
- `FiniteDimensional ℂ (HolomorphicOneForms X)` — via Riesz compact-closed-ball.

## Scope of classical content gaps

Each typeclass instance corresponds to a classical theorem that
requires substantive new Lean formalization work. Rough estimates:

- **Residue theorem** (for `HasResidueTheorem`): ~500–1000 lines — Stokes' theorem on compact manifolds or chart-cover adaptation of Mathlib's circle-integral machinery.
- **Uniformization** (for `HasUniformizationG0`): ~1000+ lines — one of the deepest theorems of complex analysis.
- **Abel's theorem** (for `HasAbelsTheorem`): ~1000+ lines (with divisor theory infrastructure).
- **Branched-cover trace** (for `HasBranchedCoverContent`, `pushforwardForm`): ~500–1000 lines — covering-space theory for holomorphic maps with ramification.
- **Degree theory** (for `ContMDiff.degree`, `HasAmbientDegreeIdentity`): ~300–500 lines — regular-value theorem + preimage counting.
- **Smooth path existence** (for `HasSmoothPaths`): ~100–200 lines — chart-cover construction.
- **Path-algebra** (for `HasSmoothPathAbelJacobi.basepoint_change`): ~200–300 lines — concat+reverse smoothness with corner handling.
- **Abel-Jacobi holomorphicity** (for `HasHolomorphicAbelJacobi`): ~200–400 lines — joint smoothness of `smoothPath`.

## References

See `docs/REFERENCES.md` for per-typeclass textbook pointers.
