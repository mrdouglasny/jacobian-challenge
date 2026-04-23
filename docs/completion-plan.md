# Completion plan: getting the remaining ~20% of the foundation

_Drafted 2026-04-23. Target: clean "foundation is solid; statements are
correct; proofs are in principle available" state for the Jacobian
Challenge._

## What "done" means

Done = **every classical theorem referenced in the axiom suite has a
correctly-typed Lean statement, non-vacuously instantiable on concrete
curves, with axiom content isolated to well-identified classical facts
that have named proof routes.**

Discharging axioms to actual Lean proofs is *not* part of this plan —
that requires major Mathlib additions (sheaf cohomology, Hodge theory,
path integration) well outside the project's scope. The plan targets
**the foundation**, not the discharge.

## Current state (entry to plan)

- 19 axioms with Lean signatures + 6 doc-only (target: all 25 with
  real Lean signatures).
- 2 concrete Track-2 curves axiom-free (`ProjectiveLine`, `Elliptic`);
  2 thin-scaffolded (`Hyperelliptic`, `PlaneCurve`).
- `ComplexTorus V L` + Jacobian bridge axiom-free modulo the 7
  Buzzard instances.
- `OneForm` with real predicates. `IsAnalyticArc` refined. `PathIntegral`
  scaffold with chart-local real def.
- No concrete genus computations on any X.
- No symplectic structure on `AnalyticCycleBasis`.

## Plan layout

Five workstreams, ordered by dependency and payoff. Each deliverable
is expected to be a single commit (or small set) passing `lake build`
with no sorries and audited via `lean_verify` on axiom deps.

---

### Workstream A: Axiom suite completion (target 100% of axioms have real Lean signatures)

#### A1. Symplectic property on `AnalyticCycleBasis` — **2 days**

Add a field `symplectic` asserting `intersectionForm`'s matrix is
`[[0, I], [-I, 0]]` in the basis. Handle the `Fin(2g)` vs `Fin(g+g)`
indexing via `Fin.castAdd`/`Fin.natAdd` + `finCongr (by ring)`.

Touches: `Jacobians/Axioms/AnalyticCycleBasis.lean`.

Unblocks: real statement of `AX_RiemannBilinear` (needs symplectic
basis).

#### A2. Promote `AX_PluckerFormula` — **1 day**

We have `PlaneCurveData` + `.genus`. State:
```
axiom AX_PluckerFormula (H : PlaneCurveData) :
    Jacobians.RiemannSurface.genus (PlaneCurve H) = H.genus
```
where `PlaneCurve H` is the (still-TODO) compactified type. If that's
blocking, axiomatize on `PlaneCurveAffine`-compatible assumption or
wait until A5 lands.

Touches: `Jacobians/Axioms/PluckerFormula.lean`.

Dependency: a working `PlaneCurve H` type. **Blocker unless we axiomatize
the type itself** — see Workstream E.

#### A3. Promote `AX_RiemannBilinear` — **2 days**

Using A1's symplectic basis, state:
```
axiom AX_RiemannBilinear (x₀ : X) :
    ∃ (b : AnalyticCycleBasis X x₀) (ω : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)),
    ∃ τ : SiegelUpperHalfSpace (genus X),
      periodMatrix_B x₀ b.isBasis ω = τ.val ∧
      (∀ i j, periodMap X x₀ (b.isBasis ⟨i.val, ...⟩) (ω j) = if i = j then 1 else 0)
```
where `periodMatrix_B` is defined by evaluating `periodMap` on the
β-cycles.

Touches: `Jacobians/Axioms/RiemannBilinear.lean`, `Jacobians/RiemannSurface/Periods.lean`
(for `periodMatrix` helper).

Unblocks: basis normalization arguments.

#### A4. Divisor / line-bundle type stubs — **2 days**

Opaque minimal stubs to support `AX_RiemannRoch`, `AX_SerreDuality`:
```
axiom Divisor (X : Type*) [...] : Type
axiom LineBundle {X} [...] (D : Divisor X) : Type
axiom Divisor.deg {X} [...] (D : Divisor X) : ℤ
axiom H0 {X} [...] (L : LineBundle D) : Type  -- global sections
axiom H1 {X} [...] (L : LineBundle D) : Type  -- first cohomology
-- each with a ℂ-vector-space structure, dim via finrank
```

Touches: new `Jacobians/RiemannSurface/LineBundle.lean` (or similar).

Not aesthetically ideal (lots of axioms), but each is a well-identified
classical object with clear discharge route via Mathlib's eventual
`AlgebraicGeometry` and complex-manifold sheaf cohomology.

#### A5. Promote `AX_RiemannRoch` + `AX_SerreDuality` — **2 days**

Using A4:
```
axiom AX_RiemannRoch (D : Divisor X) [FiniteDimensional ℂ (H0 D)] [FiniteDimensional ℂ (H1 D)] :
    (finrank ℂ (H0 D) : ℤ) - (finrank ℂ (H1 D) : ℤ) = D.deg + 1 - genus X

axiom AX_SerreDuality (D : Divisor X) :
    Nonempty ((H1 D) ≃ₗ[ℂ] Module.Dual ℂ (H0 (Ω¹ ⊗ (-D))))
```

Touches: `Jacobians/Axioms/RiemannRoch.lean`, `Jacobians/Axioms/SerreDuality.lean`.

#### A6. Promote `AX_AbelTheorem` — **1 day**

Using A4 + existing `ofCurve`-style maps. Statement: kernel of the
divisor-to-Jacobian map is exactly principal divisors.

#### A7. Promote `AX_BranchLocus` — **2 days**

Need opaque `localOrder f p q : ℕ`. Statement via `tsum` (per Gemini
review):
```
axiom AX_BranchLocus (f : X → Y) (hf : ContMDiff ...) (hnc : ¬ ∃ c, ∀ x, f x = c) :
    ∃ d : ℕ, 0 < d ∧
      (∀ q : Y, (∑' p : X, localOrder f p q) = d) ∧
      { q : Y | ∃ p : X, f p = q ∧ localOrder f p q > 1 }.Finite
```

Touches: new `Jacobians/RiemannSurface/LocalOrder.lean` or extension
of `BranchLocus.lean`.

**Deliverable**: all 25 axioms have real Lean statements. Doc-only bin
emptied.

---

### Workstream B: Concrete genus computations

These validate the framework isn't silently inconsistent on actual
curves — each needs the OneForm predicates to cut correctly on a real
X.

#### B1. `genus (ProjectiveLine) = 0` — **3-4 days**

Argument:
- `extChartAt` targets on `ProjectiveLine`: `chart0.target = chart1.target = Set.univ : Set ℂ`.
- Cocycle on overlap: `coeff₀(z) = coeff₁(1/z) · (-1/z²)` for z ≠ 0.
- `coeff₀, coeff₁` both entire.
- As `z → ∞`, `coeff₀(z) → 0` (via RHS).
- Liouville-type: entire + tends-to-0 ⟹ identically zero.

Mathlib has Liouville; argument is concrete Lean work but bounded.

Touches: new `Jacobians/ProjectiveCurve/Line/Genus.lean`.

#### B2. `genus (Elliptic ω₁ ω₂) = 1` — **3-5 days**

Argument:
- Construct `invariantOneForm : HolomorphicOneForm (Elliptic ω₁ ω₂ h)`
  from the pullback of `dz` on ℂ via the covering map `ℂ → ℂ/Λ`.
- Show it's a basis: any holomorphic 1-form on the torus is a constant
  multiple (by invariance + holomorphic).

Harder than B1 because it requires building a specific form, not just
showing all forms are zero. But the content is classical and
bounded.

Touches: new `Jacobians/ProjectiveCurve/Elliptic/Genus.lean`.

---

### Workstream C: Non-vacuous axiom witnesses

Following B1 and B2, construct concrete instances:

#### C1. `AnalyticCycleBasis.trivial` on `ProjectiveLine` — **1 day**

With `genus = 0`, `Fin (2*0) = Fin 0` is empty. Empty `loops` function.
`isBasis : Module.Basis (Fin 0) ℤ (H1 ℙ¹ x₀)`. Requires `H1(ℙ¹) = 0`
(from simple connectivity — axiomatize if needed).

Touches: new `Jacobians/ProjectiveCurve/Line/Witnesses.lean`.

#### C2. `AnalyticCycleBasis.elliptic` on `Elliptic` — **3 days**

With `genus = 1`, two loops: A-cycle `t ↦ [t · ω₁]` and B-cycle
`t ↦ [t · ω₂]` (in the quotient). Both are smooth in `t` and satisfy
`IsAnalyticArc` (linear, so analytic).

Basis of `H1(Elliptic) = ℤ²` — needs concrete computation of the
fundamental group of the torus. Mathlib has this for `Topo.IsCovering`
and `ℝⁿ/ℤⁿ` torus, but our `Elliptic` is abstracted. May need bridging.

Touches: new `Jacobians/ProjectiveCurve/Elliptic/Witnesses.lean`.

---

### Workstream D: `PathIntegral` completion (optional, defers to post-plan)

Full `pathIntegralAnalyticArc` with partition refinement, chart-
independence, homotopy invariance. Retires the `periodMap` axiom to
a real def.

**Deferred as a separate 2-3 week subproject.** Not on the critical
path to "foundation done" — `periodMap` is already axiomatized
correctly per Gemini review, so the foundation is sound without the
retirement.

---

### Workstream E: `Hyperelliptic` / `PlaneCurve` atlas (prerequisite for A2)

At minimum, we need enough type-level content that `AX_PluckerFormula`
can reference `PlaneCurve H : Type`. Options:

#### E1. Axiomatize the type and its instances — **1 day**

```
axiom PlaneCurve (H : PlaneCurveData) : Type
axiom instTopologicalSpace_PlaneCurve : TopologicalSpace (PlaneCurve H)
-- … 7 instances
```

Opaque but unblocks A2. Matches the doc-only discharge philosophy —
"statement provable in principle" via the atlas construction.

#### E2. Build the atlas (ambitious) — **2-3 weeks**

Full implicit function theorem + branch-chart construction. Out of
scope for this plan.

**Recommended: E1 now (unblocks A2), E2 as separate project.**

Similar for `Hyperelliptic`.

---

## Proposed sequence

**Phase 1 (Axiom suite completion, ~2 weeks):**
- A1 (symplectic) → A3 (RiemannBilinear) → A4 (divisor stubs) →
  A5 (Riemann-Roch + Serre) → A6 (Abel) → A7 (BranchLocus)
- E1 (type stubs for PlaneCurve, Hyperelliptic) → A2 (Plücker)

**Phase 2 (Concrete validations, ~2 weeks):**
- B1 (genus ℙ¹ = 0) → C1 (ProjectiveLine witness)
- B2 (genus Elliptic = 1) → C2 (Elliptic witness)

**Phase 3 (Optional, ~3 weeks):** D / E2 in parallel if desired.

**Total for Phases 1 + 2:** ~1 month of focused work, fitting the
CLAUDE.md "formalization takes 2-10 weeks" estimate for sister
projects.

After Phase 1 + 2, the project is at ~95% against the "foundation is
solid; statements correct; proofs in principle" criterion. Phase 3
takes it to 100% on that criterion.

Actual discharge of the classical axioms to theorems — that's a
multi-year community project tracking Mathlib's `AlgebraicGeometry`,
`ComplexManifold`, and `Hodge` developments.

## Risk assessment

- **Biggest risk:** A4 (divisor / sheaf cohomology stubs) if the
  opaque approach causes typeclass-inference tangles. Mitigation:
  test with minimal stubs first; iterate.
- **Secondary risk:** B2 (genus Elliptic) — the fundamental group of
  the torus + invariance argument is classical but the Lean encoding
  may hit Mathlib's `Covering` / quotient-space machinery. Budget
  extra days.
- **Low risk:** A1-A3, A6-A7, B1, C1 — standard Lean work with good
  primitives.

## Tracking

Each workstream item gets a task on the Claude Code task list as
its own commit lands. Progress updates to this file and to
`docs/history.md`.
