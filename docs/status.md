# Status

_Last updated: 2026-04-22 (universe lift + 8 Buzzard sorries closed)_

## Build status

✅ Green. `lake build` completes 8328 jobs. **16 sorries** (down from 24) — all in `Jacobians/Challenge.lean`. Zero sorries elsewhere.

## Sorry inventory

**8/24 Buzzard sorries closed** (2026-04-22 universe-lift commit):

* `genus` (line 47) — filled via `Jacobians.RiemannSurface.genus`.
* `Jacobian` (line 61) — filled via `Jacobians.Jacobian` (ULift-lifted).
* `AddCommGroup (Jacobian X)` instance (line 72) — via `inferInstanceAs`.
* `TopologicalSpace (Jacobian X)` instance (line 77) — via `inferInstanceAs`.
* `T2Space (Jacobian X)` instance (line 81) — via `inferInstanceAs`.
* `CompactSpace (Jacobian X)` instance (line 85) — via `inferInstanceAs`.
* `ChartedSpace (Fin (genus X) → ℂ) (Jacobian X)` instance (line 90) — via `chartedSpaceULift` transfer from `ComplexTorus`.
* `IsManifold (𝓘(ℂ, Fin (genus X) → ℂ)) ω (Jacobian X)` instance (line 96) — via `uliftHasGroupoid` transfer + `IsManifold.mk'`.

**16/24 remain.** Zero sorries outside `Challenge.lean`.

Buzzard's file required two annotation changes for the fills to compile:
* `def genus` → `noncomputable def genus` (because our `genus` routes through `Module.finrank`).
* `def Jacobian` + several instances → `noncomputable` (downstream of `Classical.choice` on the basepoint).

Type signatures are identical to Buzzard's v0.2; only `noncomputable` was added.

## Module progress

### ✅ Complete

- `Jacobians/ProjectiveCurve/Line.lean` — `ProjectiveLine := OnePoint ℂ` with all seven X-side Buzzard instances (TopologicalSpace, T2Space, CompactSpace, ConnectedSpace, Nonempty, ChartedSpace ℂ, IsManifold 𝓘(ℂ) ω). Plus `chart0`, `chart1`, `chartAt`, and `stereographic : ProjectiveLine ≃ₜ S² ⊂ ℝ³`. Zero sorries.
- `Jacobians/AbelianVariety/ComplexTorus.lean` — `ComplexTorus V L := V ⧸ L.toAddSubgroup` for a full-rank ℤ-lattice in a finite-dim ℂ-vector space. **All 7 Buzzard instances** (AddCommGroup, TopologicalSpace, IsTopologicalAddGroup, T2Space, CompactSpace, ChartedSpace V, IsManifold 𝓘(ℂ, V) ω, LieAddGroup 𝓘(ℂ, V) ω). Explicit chart atlas via fixed injectivity-ball around `0` + fixed lifts per point; chart transitions are translations by lattice vectors. Axiom-free, zero sorries.
- `Jacobians/RiemannSurface/Homology.lean` — `H1 X x₀ := Additive (Abelianization (FundamentalGroup X x₀))`. `AddCommGroup` automatic.
- `Jacobians/RiemannSurface/Genus.lean` — `genus X := Module.finrank ℂ (HolomorphicOneForm X)`. At the stub this provably returns `0` (since `HolomorphicOneForm X = ⊥`); refinement of the `OneForm.lean` predicates will widen the submodule and the axiom will become load-bearing.
- `Jacobians/Axioms/FiniteDimOneForms.lean` — `AX_FiniteDimOneForms` axiom declared; `instFiniteDimOneForms` derived from the `⊥`-submodule stub (no axiom invocation at the stub). After 2026-04-22 Gemini review: installing the instance by `:= AX_FiniteDimOneForms` on top of the previous `True ∧ True` carrier injected `False` into the environment (verified exploit in `docs/gemini-review-axioms.md`); fix lands in this same commit.

### ✅ Scaffold only

- `Jacobians/RiemannSurface/OneForm.lean` — `HolomorphicOneForm X` as `↥(⊥ : Submodule ℂ (X → ℂ → ℂ))` at the stub. The two predicates (`IsHolomorphicOneFormCoeff`, `SatisfiesCotangentCocycle`) remain `True`-stubs but are not currently used in the carrier; this keeps the submodule genuinely finite-dim (0-dim) until refinement. `AddCommGroup` + `Module ℂ` live via `abbrev` + `↥`-coercion.
- `Jacobians/AbelianVariety/Siegel.lean` — `SiegelUpperHalfSpace g` as a `Subtype` of `Matrix (Fin g) (Fin g) ℂ` with `isSymm` + `(map Complex.im).PosDef`. Four TODOs for g=1 ↔ `UpperHalfPlane`, concrete lattice from columns of `[I | τ]`, manifold structure, `Sp(2g, ℤ)`-action.
- `Jacobians/AbelianVariety/Theta.lean` — `RiemannTheta (z, τ)` defined via `tsum`. Summability, analyticity, quasi-periodicity, heat equation all TODOs.

### ✅ Scaffolding only

- `Jacobians/AbelianVariety/Lattice.lean` — convention-fixing wrapper around Mathlib's `IsZLattice` class.
- `Jacobians/AbelianVariety.lean` — top-level Part A aggregator.
- `Jacobians/ProjectiveCurve.lean` — top-level Track 2 aggregator.
- `Jacobians/ProjectiveCurve/Charts.lean` — shared-machinery stub for implicit-function-theorem chart constructions.

### ⬜ Not started

Part B (abstract `X`): `PathIntegral.lean`. `IntersectionForm.lean` + `Periods.lean` are scaffold-only.
Track 2: `Elliptic.lean`, `Hyperelliptic.lean`, `PlaneCurve.lean`.
Bridge: `AbelJacobi.lean`, `Abel.lean`, `Functoriality.lean`, `PushPull.lean`. `Jacobian/Construction.lean` is live (7 instances); `ofCurve`, `pushforward`, `pullback` definitions still pending.
Genus 0: `Uniformization.lean`.
Universe lift to match Buzzard's `Jacobian : Type u` signature (current bridge lands in `Type`).

Axioms landing tracker (2026-04-22 post-bridge):
* Declared and live: `AX_FiniteDimOneForms`, `AX_H1FreeRank2g`, `AX_PeriodInjective`, `intersectionForm` + `AX_IntersectionForm_{alternating, nondeg}`, `periodMap` (stub-axiom), `AX_PeriodLattice` + `instPeriodLatticeDiscrete`.
* Declared doc-only (concrete signature pending consumer): `AX_RiemannBilinear`, `AX_RiemannRoch`, `AX_SerreDuality`, `AX_AbelTheorem`, `AX_BranchLocus`, `AX_PluckerFormula`.

### Remaining Challenge.lean sorries (16)

#### Theorem / proof (10)
- `genus_eq_zero_iff_homeo` (58) — can't close at stub since `genus X = 0` always; opens up honestly when OneForm predicates refined.
- `ofCurve_contMDiff` (107), `ofCurve_self` (109), `ofCurve_inj` (112) — need `ofCurve` def.
- `pushforward_contMDiff` (127), `pushforward_id_apply` (130), `pushforward_comp_apply` (140)
- `pullback_contMDiff` (151), `pullback_id_apply` (154), `pullback_comp_apply` (158)
- `pushforward_pullback` (167)

#### Data (5)
- `ofCurve` (104), `pushforward` (122), `pullback` (146), `ContMDiff.degree` (164).

#### Instance (1)
- `LieAddGroup ... (Jacobian X)` (101) — requires `IsTopologicalAddGroup (ULift _)` + `ContMDiff` of add/neg transfer.

### Data sorries (pre-universe-lift breakdown, kept for history) (9)

| Symbol | Line | Kind |
|--------|------|------|
| `genus` | 44 | `def` returning `ℕ` |
| `Jacobian` | 59 | `def` returning `Type u` |
| `AddCommGroup (Jacobian X)` | 65 | instance |
| `TopologicalSpace (Jacobian X)` | 69 | instance |
| `ChartedSpace (Fin (genus X) → ℂ) (Jacobian X)` | 80 | instance |
| `Jacobian.ofCurve` | 89 | `def` |
| `Jacobian.pushforward` | 107 | `def` |
| `Jacobian.pullback` | 131 | `def` |
| `ContMDiff.degree` | 149 | `def` |

### Instance prop sorries (4)

| Symbol | Line |
|--------|------|
| `T2Space (Jacobian X)` | 72 |
| `CompactSpace (Jacobian X)` | 75 |
| `IsManifold (..) ω (Jacobian X)` | 83 |
| `LieAddGroup (..) ω (Jacobian X)` | 86 |

### Theorem sorries (11)

| Symbol | Line |
|--------|------|
| `genus_eq_zero_iff_homeo` | 53 |
| `ofCurve_contMDiff` | 92 |
| `ofCurve_self` | 94 |
| `ofCurve_inj` | 97 |
| `pushforward_contMDiff` | 110 |
| `pushforward_id_apply` | 115 |
| `pushforward_comp_apply` | 123 |
| `pullback_contMDiff` | 134 |
| `pullback_id_apply` | 139 |
| `pullback_comp_apply` | 142 |
| `pushforward_pullback` | 151 |

## Axiom inventory

**Declared, with Lean signatures (10 axioms across 6 files):**
* `AX_FiniteDimOneForms` — `Jacobians/Axioms/FiniteDimOneForms.lean`
* `AX_H1FreeRank2g` — `Jacobians/Axioms/H1FreeRank2g.lean`
* `intersectionForm` + `AX_IntersectionForm_alternating` + `AX_IntersectionForm_nondeg` — `Jacobians/Axioms/IntersectionForm.lean`
* `AX_PeriodLattice` + `instPeriodLatticeDiscrete` — `Jacobians/Axioms/PeriodLattice.lean`
* `AX_PeriodInjective` — `Jacobians/RiemannSurface/IntersectionForm.lean`
* `periodMap` (stub-axiom, to be retired by `def` once `PathIntegral` lands) — `Jacobians/RiemannSurface/Periods.lean`

**Declared doc-only (6):** `AX_RiemannBilinear`, `AX_RiemannRoch`, `AX_SerreDuality`, `AX_AbelTheorem`, `AX_BranchLocus`, `AX_PluckerFormula` — signatures sketched in their respective `Axioms/*.lean` files, concrete Lean statements deferred until the consumer module defines the missing types (`Divisor X`, `SmoothPlaneCurve F`, `localOrder`, etc.). Target signatures revised 2026-04-22 per Gemini review (existentials, `FiniteDimensional` hypotheses, ℤ-subtraction, `tsum`).

**Gemini axiom review (2026-04-22):** see [`docs/gemini-review-axioms.md`](gemini-review-axioms.md).
* ✅ Critical: `AX_FiniteDimOneForms`-as-instance + `True ∧ True` submodule stub injected `False` (verified exploit via `rank_fun_infinite`). Fix applied — submodule now `⊥`, instance derived without axiom invocation.
* ✅ Missing `AX_IntersectionForm` added as a new axiom file (intersection pairing + alternating + non-degenerate).
* ✅ `AX_RiemannBilinear` target signature revised: existentials shifted over basis choice.
* ✅ `AX_RiemannRoch` and `AX_SerreDuality` target signatures revised with `FiniteDimensional` hypotheses and ℤ-subtraction (Serre-duality now stated as an isomorphism).
* ✅ `AX_BranchLocus` target signature revised to use `tsum` + `¬ ∃ c, ∀ x, f = c` non-constant predicate.
* ✅ `AX_PeriodLattice` landed in `Jacobians/Axioms/PeriodLattice.lean`: `IsZLattice ℝ (periodLatticeInBasis X x₀ b)` in the basis-transported ambient `Fin (genus X) → ℂ`. Consumed by the Jacobian bridge.

## Jacobian bridge

`Jacobians/Jacobian/Construction.lean` lands the bridge from the abstract Riemann surface to the complex torus:

* `jacobianBasis X := Module.finBasis ℂ (HolomorphicOneForm X)` — a ℂ-basis of size `Fin (genus X)`, baked into the construction to avoid a dual `ChartedSpace` (one over `HolomorphicOneForm X →ₗ[ℂ] ℂ`, one over `Fin (genus X) → ℂ`).
* `periodLatticeInBasis X x₀ b : Submodule ℤ (Fin (genus X) → ℂ)` via `AddMonoidHom.toIntLinearMap (periodMap X x₀)` then coordinate transfer through `b.dualBasis.equivFun`.
* `Jacobian X := ComplexTorus (Fin (genus X) → ℂ) (periodLatticeInBasis X (Classical.choice ‹Nonempty X›) (jacobianBasis X))`.
* Seven Buzzard instances inherited via `change + infer_instance` off `ComplexTorus`.

**Deferred.** (a) Universe-lift wrapper: `ComplexTorus (Fin (genus X) → ℂ)` lives in `Type` but Buzzard's `Jacobian : Type u`. (b) Basepoint-independence of the lattice (needs `AX_RiemannBilinear`). (c) The Abel-Jacobi map `ofCurve P : X → Jacobian X` and its theorems. (d) Pushforward / pullback functoriality. These are the next bridge pieces.

## Dependencies pinned

- Lean: `v4.30.0-rc1`
- Mathlib: commit `8e3c989104daaa052921bf43de9eef0e1ac9fbf5` (15 April 2026)
