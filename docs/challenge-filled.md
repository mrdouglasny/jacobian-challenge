# Buzzard's Jacobian Challenge — filled-in spec with full dependency tree

_Assembled 2026-04-23. This document shows the state of the Challenge
file with every sorry replaced by a real Lean object, plus every
definition that object transitively depends on, organized in
topological order (deepest first). Proofs are elided where long and
cited-by-file-line so this stays readable._

## Legend

Every leaf in the dep tree is one of three kinds:

- ✅ **Real Lean def / theorem** — no axiom. Underlying body shown
  (or cited).
- 📐 **Prop-level classical-theorem axiom** — a `Prop` whose body is
  axiomatized but has a textbook citation. Well-formulated hypotheses,
  non-vacuous.
- ⚠️  **FUNCTION-EXISTENCE AXIOM** — 5 total, flagged with a prominent
  banner. These are `axiom foo : SomeFunctionType` — we claim such a
  function exists but don't construct it. Each has a discharge plan in
  [`docs/construction-plans/`](construction-plans/).

## Map of the 5 function-existence axioms

| # | Axiom | Type returned | File | Plan |
|---|---|---|---|---|
| ⚠1 | `pathIntegralBasepointFunctional` | `X → X → (Ω¹(X) →ₗ[ℂ] ℂ)` | `Jacobians/Axioms/AbelJacobiMap.lean:96` | [path-integral-basepoint.md](construction-plans/path-integral-basepoint.md) |
| ⚠2 | `loopIntegralToH1` | `H1 X x₀ →+ (Ω¹(X) →ₗ[ℂ] ℂ)` | `Jacobians/RiemannSurface/PathIntegral.lean:101` | [loop-integral-h1.md](construction-plans/loop-integral-h1.md) |
| ⚠3 | `pullbackOneForm` | `Ω¹(Y) →ₗ[ℂ] Ω¹(X)` | `Jacobians/Axioms/AbelJacobiMap.lean:130` | [pullback-one-form.md](construction-plans/pullback-one-form.md) |
| ⚠4 | `pushforwardOneForm` | `Ω¹(X) →ₗ[ℂ] Ω¹(Y)` | `Jacobians/Axioms/AbelJacobiMap.lean:143` | [pushforward-one-form.md](construction-plans/pushforward-one-form.md) |
| ⚠5 | `localOrder` | `ℕ` | `Jacobians/Axioms/BranchLocus.lean:62` | [local-order.md](construction-plans/local-order.md) |

---

# Dep tree, topological order

## Layer 0 — Mathlib primitives (not shown)

`ULift`, `QuotientAddGroup`, `Module.finrank`, `LinearMap`, `LinearEquiv`, `Module.Basis`, `Module.Dual`, `Submodule`, `Set`, `AddCommGroup`, `TopologicalSpace`, `T2Space`, `CompactSpace`, `ConnectedSpace`, `ChartedSpace`, `IsManifold`, `LieAddGroup`, `ContMDiff`, `HasDerivAt`, `AnalyticOn`, `fderiv`, `extChartAt`, `OnePoint`, `Homeomorph.ulift`, `IsZLattice`, `DiscreteTopology`.

All standard Mathlib. No axioms beyond Lean's core three (`propext`, `Classical.choice`, `Quot.sound`).

---

## Layer 1 — Abelian-variety infrastructure (axiom-free)

### ✅ `ComplexTorus V L` — `Jacobians/AbelianVariety/ComplexTorus.lean`

```lean
def ComplexTorus (V : Type*) [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] (L : Submodule ℤ V)
    [DiscreteTopology L] [IsZLattice ℝ L] : Type _ :=
  V ⧸ L.toAddSubgroup
```

All 7 Buzzard-required typeclass instances on `ComplexTorus V L`
(AddCommGroup, TopologicalSpace, IsTopologicalAddGroup, T2Space,
CompactSpace, ChartedSpace V, IsManifold 𝓘(ℂ, V) ω, LieAddGroup
𝓘(ℂ, V) ω) are **axiom-free** in `ComplexTorus.lean`. Charts are
explicit injectivity-ball lifts; chart transitions are translations by
lattice vectors (analytic).

---

## Layer 2 — Riemann-surface building blocks

### ✅ `HolomorphicOneForm X` — `Jacobians/RiemannSurface/OneForm.lean`

Chart-cocycle submodule.

```lean
def IsHolomorphicOneFormCoeff (X : Type*) [TopologicalSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] (coeff : X → ℂ → ℂ) : Prop :=
  ∀ x : X, AnalyticOn ℂ (coeff x) (extChartAt 𝓘(ℂ) x).target

def SatisfiesCotangentCocycle (X : Type*) [TopologicalSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] (coeff : X → ℂ → ℂ) : Prop :=
  ∀ x y : X, ∀ z ∈ (extChartAt 𝓘(ℂ) x).target,
    (extChartAt 𝓘(ℂ) x).symm z ∈ (extChartAt 𝓘(ℂ) y).source →
    coeff x z =
      coeff y ((extChartAt 𝓘(ℂ) y) ((extChartAt 𝓘(ℂ) x).symm z)) *
        (fderiv ℂ ((extChartAt 𝓘(ℂ) y) ∘ (extChartAt 𝓘(ℂ) x).symm) z 1)

noncomputable def holomorphicOneFormSubmodule (X : Type*) [...] :
    Submodule ℂ (X → ℂ → ℂ) where
  carrier := { f | IsHolomorphicOneFormCoeff X f ∧ SatisfiesCotangentCocycle X f }
  zero_mem' := ⟨fun _ => analyticOn_const, fun _ _ _ _ _ => by simp⟩
  add_mem' := -- ... (analyticOn.add + ring on the cocycle)
  smul_mem' := -- ... (const-multiplication on analyticOn + ring)

abbrev HolomorphicOneForm (X : Type*) [...] : Type _ :=
  ↥(holomorphicOneFormSubmodule X)

namespace HolomorphicOneForm
def coeff (form : HolomorphicOneForm X) : X → ℂ → ℂ := form.1
@[simp] theorem coeff_zero : (0 : HolomorphicOneForm X).coeff = 0 := rfl
@[simp] theorem coeff_add ... := rfl
@[simp] theorem coeff_smul ... := rfl
@[ext] theorem ext_of_coeff {f g} (h : f.coeff = g.coeff) : f = g :=
  Subtype.ext h
```

### 📐 `AX_FiniteDimOneForms` — `Jacobians/Axioms/FiniteDimOneForms.lean`

```lean
axiom AX_FiniteDimOneForms {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] :
    FiniteDimensional ℂ (HolomorphicOneForm X)

instance instFiniteDimOneForms : FiniteDimensional ℂ (HolomorphicOneForm X) :=
  AX_FiniteDimOneForms
```

Classical theorem (Hodge / Serre duality for compact Riemann surfaces).
Reference: Mumford Vol I §II.3; Forster IV §15.

### ✅ `genus X` — `Jacobians/RiemannSurface/Genus.lean`

```lean
noncomputable def genus (X : Type*) [...] : ℕ :=
  Module.finrank ℂ (HolomorphicOneForm X)
```

Depends on `HolomorphicOneForm` (real def) + `AX_FiniteDimOneForms` (📐).

### ✅ `H1 X x₀` — `Jacobians/RiemannSurface/Homology.lean`

```lean
abbrev H1 (X : Type*) [TopologicalSpace X] (x₀ : X) : Type _ :=
  Additive (Abelianization (FundamentalGroup X x₀))
```

Pure Mathlib (Hurewicz presentation). No project-local axioms.

---

## Layer 3 — Path integration

### ✅ `pathIntegralOnChart` — `Jacobians/RiemannSurface/PathIntegral.lean`

Chart-local path integral via `intervalIntegral`:

```lean
noncomputable def pathIntegralOnChart
    (γ : AnalyticArc X) (p : X) (form : HolomorphicOneForm X) : ℂ :=
  ∫ r in (0 : ℝ)..1,
    form.coeff p ((extChartAt 𝓘(ℂ) p) (γ.extend r)) *
      derivWithin (fun s : ℝ => (extChartAt 𝓘(ℂ) p) (γ.extend s))
        (Set.Ioo (0 : ℝ) 1) r
```

Real def, axiom-free at the chart-local level.

### ⚠️ EXISTENCE AXIOM #2 of 5 — `loopIntegralToH1`

```
╔══════════════════════════════════════════════════════════════════╗
║  ⚠️  FUNCTION-EXISTENCE AXIOM #2 of 5                             ║
║                                                                   ║
║  `loopIntegralToH1 x₀ : H1 X x₀ →+ (Ω¹(X) →ₗ[ℂ] ℂ)`               ║
║                                                                   ║
║  Classical content: the H_1-level period pairing                  ║
║  `[γ] ↦ (ω ↦ ∫_γ ω)`. Well-definedness on H_1 packages:          ║
║    (i) multi-chart path integration,                              ║
║    (ii) homotopy invariance (Cauchy on chart disks + Stokes       ║
║         on homotopy rectangle),                                   ║
║    (iii) additivity over loop concatenation (π_1 → Ab → Additive).║
║                                                                   ║
║  Discharge plan: docs/construction-plans/loop-integral-h1.md      ║
║  (~1.5 weeks on top of Plan #1 infrastructure)                    ║
╚══════════════════════════════════════════════════════════════════╝
```

```lean
axiom loopIntegralToH1 {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (x₀ : X) :
    H1 X x₀ →+ (HolomorphicOneForm X →ₗ[ℂ] ℂ)
```

### ✅ `periodMap X x₀` — `Jacobians/RiemannSurface/Periods.lean`

```lean
noncomputable def periodMap (X : Type*) [...] (x₀ : X) :
    H1 X x₀ →+ (HolomorphicOneForm X →ₗ[ℂ] ℂ) :=
  loopIntegralToH1 x₀
```

Real `def` routing through ⚠️ axiom #2.

---

## Layer 4 — Period lattice in basis coordinates

### ✅ `jacobianBasis X` — `Jacobians/Jacobian/Construction.lean`

```lean
noncomputable def jacobianBasis (X : Type*) [...] :
    Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X) :=
  Module.finBasis ℂ (HolomorphicOneForm X)
```

Uses `FiniteDimensional ℂ (HolomorphicOneForm X)` from `AX_FiniteDimOneForms`.

### ✅ `periodMapInBasis`, `periodLatticeInBasis` — `Jacobians/Axioms/PeriodLattice.lean`

```lean
noncomputable def periodMapInBasis (X : Type*) [...] (x₀ : X)
    (b : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) :
    H1 X x₀ →ₗ[ℤ] (Fin (genus X) → ℂ) :=
  (b.dualBasis.equivFun.toLinearMap.restrictScalars ℤ).comp
    (periodMap X x₀).toIntLinearMap

noncomputable def periodLatticeInBasis (X : Type*) [...] (x₀ : X)
    (b : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) :
    Submodule ℤ (Fin (genus X) → ℂ) :=
  LinearMap.range (periodMapInBasis X x₀ b)
```

### 📐 `AX_PeriodLattice`, `instPeriodLatticeDiscrete` — same file

```lean
axiom instPeriodLatticeDiscrete (X : Type*) [...] (x₀ : X) (b : ...) :
    DiscreteTopology (periodLatticeInBasis X x₀ b)

axiom AX_PeriodLattice (X : Type*) [...] (x₀ : X) (b : ...) :
    IsZLattice ℝ (periodLatticeInBasis X x₀ b)
```

Classical: Riemann bilinear relations. Mumford II §2.

---

## Layer 5 — Form-level primitives

### ⚠️ EXISTENCE AXIOM #1 of 5 — `pathIntegralBasepointFunctional`

```
╔══════════════════════════════════════════════════════════════════╗
║  ⚠️  FUNCTION-EXISTENCE AXIOM #1 of 5                             ║
║                                                                   ║
║  `pathIntegralBasepointFunctional X P₀ P : Ω¹(X) →ₗ[ℂ] ℂ`        ║
║                                                                   ║
║  Classical content: for fixed endpoints, returns ω ↦ ∫_{P₀}^P ω  ║
║  (a ℂ-linear functional on 1-forms). Path-choice made via         ║
║  Classical.choice on a piecewise-real-analytic arc.               ║
║                                                                   ║
║  Paired with `AX_pathIntegral_local_antiderivative` below, which  ║
║  BINDS this functional to the 1-form cocycle via the FTC —        ║
║  without that pairing, the axiom is too weak (could be trivial).  ║
║                                                                   ║
║  Discharge plan: docs/construction-plans/path-integral-basepoint.md║
║  (~2 weeks, shared infra with axiom #2)                           ║
╚══════════════════════════════════════════════════════════════════╝
```

```lean
axiom pathIntegralBasepointFunctional (X : Type*) [...] (P₀ P : X) :
    HolomorphicOneForm X →ₗ[ℂ] ℂ
```

### 📐 `AX_pathIntegral_local_antiderivative`

```lean
axiom AX_pathIntegral_local_antiderivative (X : Type*) [...]
    (P₀ P : X) (form : HolomorphicOneForm X) :
    HasDerivAt
      (fun z : ℂ =>
        pathIntegralBasepointFunctional X P₀ ((extChartAt 𝓘(ℂ) P).symm z) form)
      (form.coeff P ((extChartAt 𝓘(ℂ) P) P))
      ((extChartAt 𝓘(ℂ) P) P)
```

FTC localised to a chart. Binds axiom #1 to the `HolomorphicOneForm`
cocycle, eliminating the trivial-zero unsoundness pathway.

### ⚠️ EXISTENCE AXIOM #3 of 5 — `pullbackOneForm`

```
╔══════════════════════════════════════════════════════════════════╗
║  ⚠️  FUNCTION-EXISTENCE AXIOM #3 of 5                             ║
║                                                                   ║
║  `pullbackOneForm f hf : Ω¹(Y) →ₗ[ℂ] Ω¹(X)`                       ║
║                                                                   ║
║  Classical content: (f^* ω)(x) = ω(f(x)) · df(x) dx in chart      ║
║  coords. Linearity obvious; cocycle-preservation uses chain rule. ║
║                                                                   ║
║  Discharge plan: docs/construction-plans/pullback-one-form.md     ║
║  (~1.5 weeks; unlocks 5+ downstream theorem retirements)          ║
╚══════════════════════════════════════════════════════════════════╝
```

```lean
axiom pullbackOneForm {X Y} [...] (f : X → Y) (_hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    HolomorphicOneForm Y →ₗ[ℂ] HolomorphicOneForm X
```

### ⚠️ EXISTENCE AXIOM #4 of 5 — `pushforwardOneForm`

```
╔══════════════════════════════════════════════════════════════════╗
║  ⚠️  FUNCTION-EXISTENCE AXIOM #4 of 5                             ║
║                                                                   ║
║  `pushforwardOneForm f hf : Ω¹(X) →ₗ[ℂ] Ω¹(Y)`                    ║
║                                                                   ║
║  Classical content: trace / transfer of 1-forms under a finite    ║
║  branched cover. `(f_* ω)(q) = Σ_{p ∈ f⁻¹(q)} ω(p)/f'(p)`         ║
║  with multiplicities from localOrder (#5). Zero for constant f.   ║
║                                                                   ║
║  Discharge plan: docs/construction-plans/pushforward-one-form.md  ║
║  (~2 weeks, after #5)                                             ║
╚══════════════════════════════════════════════════════════════════╝
```

```lean
axiom pushforwardOneForm {X Y} [...] (f : X → Y) (_hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    HolomorphicOneForm X →ₗ[ℂ] HolomorphicOneForm Y
```

### 📐 Form-level functoriality axioms

```lean
axiom AX_pullbackOneForm_id : pullbackOneForm id contMDiff_id = LinearMap.id
axiom AX_pullbackOneForm_comp :
    pullbackOneForm (g ∘ f) (hg.comp hf) =
      (pullbackOneForm f hf).comp (pullbackOneForm g hg)
axiom AX_pushforwardOneForm_id ...
axiom AX_pushforwardOneForm_comp ...
```

Atomic classical facts (pullback is contravariant functor on 1-forms).

---

## Layer 6 — Ambient linear maps (derived)

### ✅ `pushforwardAmbientLinear` — `Jacobians/Axioms/AbelJacobiMap.lean`

```lean
noncomputable def pushforwardAmbientLinear {X Y} [...] (f hf) :
    (Fin (genus X) → ℂ) →ₗ[ℂ] (Fin (genus Y) → ℂ) :=
  let eX := (jacobianBasis X).dualBasis.equivFun
  let eY := (jacobianBasis Y).dualBasis.equivFun
  eY.toLinearMap.comp ((pullbackOneForm f hf).dualMap.comp eX.symm.toLinearMap)
```

Real def; uses `pullbackOneForm` (⚠️ #3) + basis dualisation.

### ✅ `pullbackAmbientLinear` — symmetric via `pushforwardOneForm` (⚠️ #4).

### 📐 Lattice-preservation axioms

```lean
axiom AX_pushforwardAmbient_preserves_lattice ...
axiom AX_pullbackAmbient_preserves_lattice ...
```

Period-map naturality: `∫_{f_*γ} ω_Y = ∫_γ (pullbackOneForm f) ω_Y`.

---

## Layer 7 — Jacobian quotient machinery

### ✅ `jacobianHomOfAmbient` — helper def

```lean
noncomputable def jacobianHomOfAmbient
    (X Y : ...) (L : (Fin (genus X) → ℂ) →ₗ[ℂ] (Fin (genus Y) → ℂ))
    (hL : ∀ v ∈ L_X, L v ∈ L_Y) : Jacobian X →ₜ+ Jacobian Y :=
  { toFun := fun p => ULift.up (QuotientAddGroup.map _ _ L.toAddMonoidHom hL p.down)
    map_zero' := by apply ULift.ext; exact map_zero _
    map_add' := ...
    continuous_toFun := ...}
```

Real def; combines finite-dim continuity + quotient continuity + ULift wrap.

### ✅ `Jacobian X` — `Jacobians/Jacobian/Construction.lean`

```lean
noncomputable abbrev JacobianAmbient (X : Type*) [...] : Type :=
  ComplexTorus (Fin (genus X) → ℂ)
    (periodLatticeInBasis X (Classical.arbitrary X) (jacobianBasis X))

noncomputable abbrev Jacobian (X : Type u) [...] : Type u :=
  ULift.{u, 0} (JacobianAmbient X)
```

All 7 Buzzard typeclass instances real:
- `AddCommGroup`, `TopologicalSpace`, `T2Space`, `CompactSpace` — ULift transfer.
- `ChartedSpace (Fin (genus X) → ℂ)` — via `chartedSpaceULift`.
- `IsManifold 𝓘(ℂ) ω` — via `uliftHasGroupoid`.
- `LieAddGroup 𝓘(ℂ) ω` — via `contMDiff_ulift_up` / `contMDiff_ulift_down` bridge lemmas composed with `LieAddGroup (ComplexTorus V L)`.

### ✅ ULift bridge lemmas (real theorems)

```lean
theorem extChartAt_source_up_iff ...
theorem extChartAt_target_iff ...
theorem contMDiff_ulift_up : ContMDiff I I ω (ULift.up : JacobianAmbient X → Jacobian X)
theorem contMDiff_ulift_down : ContMDiff I I ω (ULift.down : Jacobian X → JacobianAmbient X)
```

---

## Layer 8 — Abel-Jacobi, pushforward, pullback, degree

### ✅ `ofCurveAmbient` — `Jacobians/Axioms/AbelJacobiMap.lean:157`

```lean
noncomputable def ofCurveAmbient (X : Type u) [...] : X → X → (Fin (genus X) → ℂ) :=
  fun P₀ P i => pathIntegralBasepointFunctional X P₀ P (jacobianBasis X i)
```

Real def. Uses ⚠️ axiom #1.

### ✅ `ofCurveImpl` — real def

```lean
noncomputable def ofCurveImpl (X : Type u) [...] (P₀ : X) : X → Jacobian X :=
  fun P => ULift.up <|
    QuotientAddGroup.mk' _ (ofCurveAmbient X P₀ P - ofCurveAmbient X P₀ P₀)
```

Basepoint subtraction makes `ofCurveImpl X P₀ P₀ = 0` definitional.

### ✅ `pushforwardImpl`, `pullbackImpl` — real defs

```lean
noncomputable def pushforwardImpl (X) [...] (Y) [...] (f hf) :
    Jacobian X →ₜ+ Jacobian Y :=
  jacobianHomOfAmbient X Y (pushforwardAmbientLinear f hf)
    (AX_pushforwardAmbient_preserves_lattice f hf)

noncomputable def pullbackImpl (X) [...] (Y) [...] (f hf) :
    Jacobian Y →ₜ+ Jacobian X :=
  jacobianHomOfAmbient Y X (pullbackAmbientLinear f hf)
    (AX_pullbackAmbient_preserves_lattice f hf)
```

### ⚠️ EXISTENCE AXIOM #5 of 5 — `localOrder`

```
╔══════════════════════════════════════════════════════════════════╗
║  ⚠️  FUNCTION-EXISTENCE AXIOM #5 of 5                             ║
║                                                                   ║
║  `localOrder f p q : ℕ`                                           ║
║                                                                   ║
║  Classical content: order of zero of `z ↦ f(z) - q` at p in       ║
║  chart coords. 0 if f p ≠ q; ≥ 1 if f p = q and f non-constant.   ║
║  Well-defined because non-constant holomorphic maps have          ║
║  isolated zeros of finite order.                                  ║
║                                                                   ║
║  Discharge plan: docs/construction-plans/local-order.md           ║
║  (~1 week, cheapest of the 5)                                     ║
╚══════════════════════════════════════════════════════════════════╝
```

```lean
axiom localOrder {X Y : Type*} [...] (f : X → Y) (p : X) (q : Y) : ℕ
```

### 📐 `AX_BranchLocus` — depends on `localOrder`

```lean
axiom AX_BranchLocus {X Y} [...] (f : X → Y) (_hf : ContMDiff ...) 
    (_hnc : ¬ ∃ c : Y, ∀ x : X, f x = c) :
    ∃ d : ℕ, 0 < d ∧
      (∀ q : Y, (∑' p : X, localOrder f p q) = d) ∧
      { q : Y | ∃ p : X, f p = q ∧ localOrder f p q > 1 }.Finite
```

Classical: open mapping theorem + compactness. Forster I §4.

### ✅ `degreeImpl` — real def

```lean
noncomputable def degreeImpl {X Y} [...] (f : X → Y) (hf : ContMDiff ...) : ℕ := by
  classical
  exact if hc : ∃ c : Y, ∀ x : X, f x = c then 0
        else Classical.choose (AX_BranchLocus f hf hc)
```

Uses ⚠️ axiom #5 (`localOrder`) + 📐 axiom (`AX_BranchLocus`).

---

## Layer 9 — Property theorems (partly derived, partly axiom)

### ✅ Derived theorems

- `AX_ofCurve_self : ofCurveImpl X P P = 0` — by `unfold + ext + simp + rfl` (basepoint subtraction).
- `AX_jacobian_lieAddGroup : LieAddGroup ... (Jacobian X)` — `by infer_instance` (via Layer 7 ULift bridge lemmas).
- `AX_pushforward_id_apply : pushforwardImpl X X id _ P = P` — via `pushforwardAmbientLinear_id` (derived from `AX_pullbackOneForm_id` + `LinearMap.dualMap_id`) + `jacobianHomOfAmbient_id_apply`.
- `AX_pushforward_comp_apply : pushforwardImpl X Z (g ∘ f) _ P = pushforwardImpl Y Z g _ (pushforwardImpl X Y f _ P)` — via `pushforwardAmbientLinear_comp` (derived from `AX_pullbackOneForm_comp` + `LinearMap.dualMap_comp_dualMap`) + `jacobianHomOfAmbient_comp_apply`.
- `AX_pullback_id_apply`, `AX_pullback_comp_apply` — symmetric.

### 📐 Remaining property axioms (classical theorems)

- `AX_ofCurve_contMDiff` — Abel-Jacobi map is holomorphic.
- `AX_ofCurve_inj` — Abel's theorem (injectivity in positive genus).
- `AX_pushforward_contMDiff`, `AX_pullback_contMDiff` — smoothness of push/pull on Jacobians.
- `AX_pushforward_pullback : pushforward ∘ pullback = deg • id` — the deepest §24 classical identity.
- `AX_genus_eq_zero_iff_homeo` — uniformization for genus 0.

All five are classical theorems with textbook citations; each retires via a dedicated proof project.

---

# Layer 10 — Buzzard's Challenge.lean, filled in

`Jacobians/Challenge.lean`, verbatim structure with real bodies:

```lean
import Mathlib -- pin 8e3c989 (15 April 2026)
import Jacobians.Jacobian
import Jacobians.Axioms.AbelJacobiMap
import Jacobians.Axioms.Uniformization0

open scoped ContDiff
open scoped Manifold

/-- §1. -/
noncomputable def genus (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] : ℕ :=
  Jacobians.RiemannSurface.genus X

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- §14 (hack-blocker). -/
lemma genus_eq_zero_iff_homeo :
    genus X = 0 ↔ Nonempty (X ≃ₜ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) := by
  change Jacobians.RiemannSurface.genus X = 0 ↔ _
  exact Jacobians.Axioms.AX_genus_eq_zero_iff_homeo

universe u in
/-- §2. -/
noncomputable def Jacobian (X : Type u) [...] : Type u :=
  Jacobians.Jacobian X

namespace Jacobian

/-- §§3–9. All 7 typeclass instances. -/
noncomputable instance : AddCommGroup (Jacobian X) := inferInstance
noncomputable instance : TopologicalSpace (Jacobian X) := inferInstance
instance : T2Space (Jacobian X) := inferInstance
instance : CompactSpace (Jacobian X) := inferInstance
noncomputable instance : ChartedSpace (Fin (genus X) → ℂ) (Jacobian X) := by
  change ChartedSpace (Fin (Jacobians.RiemannSurface.genus X) → ℂ) (Jacobians.Jacobian X)
  infer_instance
instance : IsManifold (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω (Jacobian X) := by
  change IsManifold ... ω (Jacobians.Jacobian X)
  infer_instance
instance : LieAddGroup (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω (Jacobian X) := by
  change LieAddGroup ... ω (Jacobians.Jacobian X)
  infer_instance

/-- §10. -/
noncomputable def ofCurve (P : X) : X → Jacobian X := Jacobians.Axioms.ofCurveImpl X P

lemma ofCurve_contMDiff (P : X) : ContMDiff 𝓘(ℂ) ... ω (ofCurve P) :=
  Jacobians.Axioms.AX_ofCurve_contMDiff P  -- 📐 §15

lemma ofCurve_self (P : X) : ofCurve P P = 0 :=
  Jacobians.Axioms.AX_ofCurve_self P  -- ✅ derived

lemma ofCurve_inj (P : X) (h : 0 < genus X) : Function.Injective (ofCurve P) :=
  Jacobians.Axioms.AX_ofCurve_inj P h  -- 📐 §17 (Abel's theorem)

/-- §12. -/
noncomputable def pushforward (f : X → Y) (hf : ContMDiff ... ω f) :
    Jacobian X →ₜ+ Jacobian Y :=
  Jacobians.Axioms.pushforwardImpl X Y f hf

theorem pushforward_contMDiff : ContMDiff ... ω (pushforward f hf) :=
  Jacobians.Axioms.AX_pushforward_contMDiff f hf  -- 📐 §18

lemma pushforward_id_apply (P : Jacobian X) : pushforward id contMDiff_id P = P :=
  Jacobians.Axioms.AX_pushforward_id_apply P  -- ✅ derived

lemma pushforward_comp_apply (P : Jacobian X) :
    pushforward (g ∘ f) (hg.comp hf) P = pushforward g hg (pushforward f hf P) :=
  Jacobians.Axioms.AX_pushforward_comp_apply f hf g hg P  -- ✅ derived

/-- §13. -/
noncomputable def pullback (f : X → Y) (hf : ContMDiff ... ω f) :
    Jacobian Y →ₜ+ Jacobian X :=
  Jacobians.Axioms.pullbackImpl X Y f hf

theorem pullback_contMDiff : ContMDiff ... ω (pullback f hf) :=
  Jacobians.Axioms.AX_pullback_contMDiff f hf  -- 📐 §21

lemma pullback_id_apply (P : Jacobian X) : pullback id contMDiff_id P = P :=
  Jacobians.Axioms.AX_pullback_id_apply P  -- ✅ derived

lemma pullback_comp_apply (P : Jacobian Z) :
    pullback (g.comp f) (hg.comp hf) P = pullback f hf (pullback g hg P) :=
  Jacobians.Axioms.AX_pullback_comp_apply f hf g hg P  -- ✅ derived

/-- §11. -/
noncomputable def _root_.ContMDiff.degree (hf : ContMDiff ... ω f) : ℕ :=
  Jacobians.Axioms.degreeImpl f hf

/-- §24. -/
lemma pushforward_pullback (P : Jacobian Y) :
  pushforward f hf (pullback f hf P) = (ContMDiff.degree f hf) • P :=
  Jacobians.Axioms.AX_pushforward_pullback f hf P  -- 📐 deepest

end Jacobian
```

---

# Summary

**Every Buzzard-exposed definition (§§1–13) is a real Lean `def`/`instance`.** Tracing the dependency chain of every one of these, the tree terminates at:

- **Real Lean defs** — the vast majority of intermediate constructions
  (`ComplexTorus`, `HolomorphicOneForm` submodule, `jacobianBasis`, `periodMap`, `periodLatticeInBasis`, `ofCurveImpl`, `pushforwardImpl`, `pullbackImpl`, `degreeImpl`, `ULift` bridge lemmas, `jacobianHomOfAmbient`, `pushforwardAmbientLinear`, `pullbackAmbientLinear`, …).
- **Mathlib primitives** — standard library.
- **📐 Classical-theorem axioms** (Prop-level) — 10 total: `AX_FiniteDimOneForms`, `AX_pathIntegral_local_antiderivative`, `AX_pullbackOneForm_id`, `AX_pullbackOneForm_comp`, `AX_pushforwardOneForm_id`, `AX_pushforwardOneForm_comp`, `AX_pushforwardAmbient_preserves_lattice`, `AX_pullbackAmbient_preserves_lattice`, `AX_PeriodLattice`, `instPeriodLatticeDiscrete`, `AX_BranchLocus`. Each with a textbook citation.
- **⚠️ Function-existence axioms** — **exactly 5**:
  1. `pathIntegralBasepointFunctional`
  2. `loopIntegralToH1`
  3. `pullbackOneForm`
  4. `pushforwardOneForm`
  5. `localOrder`

These 5 are the only non-real-def leaves in the entire dep graph. All documented in [`docs/construction-plans/`](construction-plans/); total ~5–6 weeks discharge estimate for a focused contributor.

Plus 6 **📐 property-theorem axioms at the Challenge interface** (uniformization, holomorphicity of Abel-Jacobi, Abel's theorem, holomorphicity of pushforward/pullback, `pushforward_pullback = deg • id`) — deep classical theorems, each needs its own multi-week proof project.
