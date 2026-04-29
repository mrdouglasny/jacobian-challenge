# Dependency trace — foundation closure audit

_Drafted 2026-04-23. Updated 2026-04-29._

**Update note (2026-04-29):** since the original draft, two important
changes:
1. `AX_FiniteDimOneForms` is **retired**. Finite-dimensionality now
   derives from Kirov's Montel theorem via the real
   `Jacobians.Bridge.KirovHolomorphic` bridge (commit `dfe57b0` and
   subsequent). The aggregate axiom list below still references it for
   historical traceability — read the row as "now derived, not asserted".
2. A new **3-level Liouville axiom hierarchy** lives at
   `Jacobians/Axioms/HyperellipticLiouville.lean`. It is *not* used by
   any foundation `def` (genus, Jacobian, ofCurve, …); it is consumed
   only by the hyperelliptic test theorem `genus_HyperellipticEven_eq`.
   Listed in §A-test below for completeness.

_Original purpose: for each foundation definition to claim it is closed,
everything it depends on must be complete or else a hard theorem stated
as an axiom. This document traces the transitive dependencies of every
F-class and H-class (foundation) definition in Buzzard's `Challenge.lean`,
and classifies each dependency as (R) real def/instance or (A)
properly-formulated axiom._

**Legend:**
- **R** = real `def` / `instance` / derived theorem. No axiom invoked.
- **A-deep** = axiom, classical theorem (cited textbook, multi-page proof).
- **A-infra** = axiom, technical Lean/Mathlib infrastructure gap (not a classical-theorem obstruction).
- **⚠** = flag: needs revisiting.

## 1. `def genus X`

Defined as `Jacobians.RiemannSurface.genus X := Module.finrank ℂ (HolomorphicOneForm X)`.

| Dep | Location | Status |
|---|---|---|
| `Module.finrank` | Mathlib | R |
| `HolomorphicOneForm X` | `OneForm.lean` (chart-cocycle submodule; predicates are real `AnalyticOn` + chart-derivative formula) | R |
| `IsHolomorphicOneFormCoeff` | `OneForm.lean` | R |
| `SatisfiesCotangentCocycle` | `OneForm.lean` | R |
| `AX_FiniteDimOneForms` | `Axioms/FiniteDimOneForms.lean` | **A-deep**: finite-dim of `Ω¹(X)` for compact Riemann surface. Hodge / Serre-duality route (Mumford Vol I §II.3; Forster IV §15). Hypotheses: T2 + compact + connected + `ChartedSpace ℂ` + `IsManifold 𝓘(ℂ) ω`. Well-formulated, non-vacuous now that carrier isn't `⊥`. |

**Closure**: ✓ all deps bottom out at R or A-deep.

## 2. `def Jacobian X`

Defined as `ULift (ComplexTorus (Fin (genus X) → ℂ) (periodLatticeInBasis X x₀ jacobianBasis))`.

| Dep | Location | Status |
|---|---|---|
| `ULift`, `ComplexTorus`, `⧸` | Mathlib + `ComplexTorus.lean` (real abbrev) | R |
| `genus X` | §1 | R (deps to A-deep) |
| `jacobianBasis X := Module.finBasis ℂ (HolomorphicOneForm X)` | `Construction.lean` | R (needs `FiniteDimensional` → A-deep `AX_FiniteDimOneForms`) |
| `periodLatticeInBasis X x₀ b := LinearMap.range (periodMapInBasis ...)` | `Axioms/PeriodLattice.lean` | R |
| `periodMapInBasis` | same file | R (Mathlib linear-map composition) |
| `periodMap X x₀` | `Periods.lean` | R — `def` via `loopIntegralToH1` |
| `loopIntegralToH1 x₀` | `PathIntegral.lean` | **A-deep**: path-integral descent to H₁. Packages multi-chart path integration + homotopy invariance + linearity. Hypotheses: T2 + compact + connected + ChartedSpace ℂ + IsManifold. Mumford Vol I §II.2; Forster I §10–13. |
| `Classical.arbitrary X` | needs `Nonempty X` | R (Buzzard's hypothesis) |

**Closure**: ✓.

## 3. `instance AddCommGroup (Jacobian X)`

Via `inferInstanceAs (AddCommGroup (ULift (JacobianAmbient X)))`.

| Dep | Location | Status |
|---|---|---|
| `ComplexTorus.instAddCommGroup` | `ComplexTorus.lean` | R (`QuotientAddGroup`) |
| ULift transfer | Mathlib | R |

**Closure**: ✓ (inherits §2's A-deep deps transitively).

## 4. `instance TopologicalSpace (Jacobian X)`

Analogous. All R.

## 5. `instance T2Space (Jacobian X)` **(H)**

Via `ComplexTorus.instT2Space` + ULift. Requires lattice discreteness.

| Dep | Status |
|---|---|
| `instPeriodLatticeDiscrete` | **A-deep**: period lattice is discrete in `Fin (genus X) → ℂ`. Follows from `AX_RiemannBilinear` (positive-definite imaginary part of period matrix ⇒ discrete). Mumford Vol I §II.4. |

**Closure**: ✓.

## 6. `instance CompactSpace (Jacobian X)` **(H)**

Via `ComplexTorus.instCompactSpace` + ULift. Requires full-rank lattice.

| Dep | Status |
|---|---|
| `AX_PeriodLattice` | **A-deep**: period image is `IsZLattice` (2g-rank ℤ-lattice in `ℝ^(2g)` ≅ `ℂ^g`). Riemann bilinear relations + rank(H₁) = 2g. Mumford II §2; Griffiths-Harris Ch. 2 §2. |

**Closure**: ✓.

## 7. `instance ChartedSpace (Fin (genus X) → ℂ) (Jacobian X)`

Via `chartedSpaceULift` + `ComplexTorus.chartedSpace`. All R.

| Dep | Status |
|---|---|
| `ComplexTorus.chartedSpace` | R (axiom-free in `ComplexTorus.lean` — explicit injectivity-ball + lattice lifts) |
| `chartedSpaceULift` | R |

**Closure**: ✓ (no axiom beyond §2's propagation).

## 8. `instance IsManifold 𝓘(ℂ) ω (Jacobian X)` **(H)**

Via `uliftHasGroupoid` + `IsManifold.mk'`. All R (chart transitions are translations by lattice vectors → analytic).

**Closure**: ✓.

## 9. `instance LieAddGroup 𝓘(ℂ) ω (Jacobian X)` **(H → closed 2026-04-23)**

**Real instance**, no axiom. Closed via ULift-smoothness lemmas.

| Dep | Status |
|---|---|
| `contMDiff_ulift_up`, `contMDiff_ulift_down` | R — proved in `Jacobian/Construction.lean` using bridge lemmas `extChartAt_source_up_iff` and `extChartAt_target_iff` that establish propositional (not `rfl`) equivalence of chart sources and targets between `Jacobian X` and `JacobianAmbient X` |
| `LieAddGroup (ComplexTorus V L)` | R (axiom-free in `AbelianVariety/ComplexTorus.lean`) |
| `ContMDiff.comp`, `ContMDiff.prodMk`, `contMDiff_add`, `contMDiff_neg` | R (Mathlib) |

**Closure**: ✓. The `AX_jacobian_lieAddGroup` axiom is retained as a `theorem` signature (not an `axiom`) for downstream stability; its body is `by infer_instance`.

## 10. `def Jacobian.ofCurve P`

Via `ofCurveImpl := ULift.up ∘ mk' ∘ (ofCurveAmbient X P₀ · - ofCurveAmbient X P₀ P₀)`.

| Dep | Status |
|---|---|
| `ofCurveAmbient P₀ P i := pathIntegralBasepointFunctional X P₀ P (jacobianBasis X i)` | R |
| `pathIntegralBasepointFunctional` | **A-deep** (weak alone) |
| `AX_pathIntegral_local_antiderivative` | **A-deep**: Fundamental Theorem of Calculus localised to chart. Binds the functional to `form.coeff P (chart P)` via `HasDerivAt`. Prevents trivial-zero satisfaction — makes the primitive genuinely load-bearing. |
| `jacobianBasis X` | R (via A-deep `AX_FiniteDimOneForms`) |
| `QuotientAddGroup.mk'`, `ULift.up` | Mathlib | R |

**Closure**: ✓.

## 11. `def Jacobian.pushforward f hf`

Via `pushforwardImpl := jacobianHomOfAmbient X Y (pushforwardAmbientLinear f hf) ...`.

| Dep | Status |
|---|---|
| `jacobianHomOfAmbient` | R (uses `QuotientAddGroup.map`, `.toContinuousLinearMap`, ULift — all Mathlib) |
| `pushforwardAmbientLinear f hf := eY ∘ (pullbackOneForm f hf).dualMap ∘ eX.symm` | R (derived via `.dualMap` + basis dualisation) |
| `pullbackOneForm f hf` | **A-deep**: pullback of holomorphic 1-forms along `f : X → Y`, as ℂ-linear map. Classical: `f^* ω := ω ∘ df` on cocycle data. Cocycle-preservation uses holomorphicity of `f`. Retires with manifold-cotangent-bundle API. |
| `(jacobianBasis X).dualBasis.equivFun` | R (Mathlib basis machinery on finite-dim module) |
| `AX_pushforwardAmbient_preserves_lattice f hf` | **A-deep**: pushforward maps period lattice of `X` into period lattice of `Y`. Follows from period-map naturality `∫_{f_*γ} ω_Y = ∫_γ (pullbackOneForm f) ω_Y` combined with `f_*` sending integer cycles to integer cycles. |

**Closure**: ✓.

## 12. `def Jacobian.pullback f hf`

Symmetric to §11, using `pushforwardOneForm` + `AX_pullbackAmbient_preserves_lattice`.

| Dep | Status |
|---|---|
| `pullbackAmbientLinear f hf := eX ∘ (pushforwardOneForm f hf).dualMap ∘ eY.symm` | R |
| `pushforwardOneForm f hf` | **A-deep**: trace / pushforward of 1-forms along a finite cover. Classical: `(f_* ω)(q) = Σ_{p ∈ f⁻¹(q)} ω(p) / f'(p)` weighted by local multiplicity. Zero for constant `f`. Forster I §6. |
| `AX_pullbackAmbient_preserves_lattice` | **A-deep**: symmetric to §11's lattice-preservation. |

**Closure**: ✓.

## 13. `def ContMDiff.degree f hf`

Via `degreeImpl := if ∃ c, ∀ x, f x = c then 0 else Classical.choose (AX_BranchLocus f hf hc)`.

| Dep | Status |
|---|---|
| `AX_BranchLocus f hf hnc` | **A-deep**: for non-constant holomorphic `f : X → Y` between compact Riemann surfaces, ∃ `d > 0` with `∀ q : Y, ∑' p, localOrder f p q = d`, and the branch locus is finite. Open mapping theorem (dim 1) + compactness. Forster I §4. |
| `localOrder f p q` | **A-deep**: opaque `ℕ` — local multiplicity of `f` at `p` above `q`. Well-defined because 1-dim holomorphic maps have isolated zeros. |
| `Classical.choose` | Lean core | R |

**Closure**: ✓.

## 16. `theorem ofCurve_self : ofCurve P P = 0`

**R** — derived from basepoint subtraction in `ofCurveImpl`. No axiom.

---

## Aggregate — complete axiom list on which the foundation rests

### A-deep (classical theorems; textbook-citable):

| # | Axiom | Classical statement | Reference |
|---|---|---|---|
| 1 | `AX_FiniteDimOneForms` | dim Ω¹(X) < ∞ for compact X | Mumford II§3; Forster IV§15 |
| 2 | `loopIntegralToH1` | ∫ descends to H₁ (multi-chart + homotopy) | Mumford I§II.2 |
| 3 | `pathIntegralBasepointFunctional` | ∫_{P₀}^P ω as linear in ω | (primitive; bound by #4) |
| 4 | `AX_pathIntegral_local_antiderivative` | chart-local FTC | Standard |
| 5 | `pullbackOneForm f hf` | pullback of 1-forms along holomorphic | Standard |
| 6 | `pushforwardOneForm f hf` | trace of 1-forms (finite cover) | Forster I§6 |
| 7 | `AX_pushforwardAmbient_preserves_lattice` | period-naturality (push) | Mumford I§II.4 |
| 8 | `AX_pullbackAmbient_preserves_lattice` | period-naturality (pull) | same |
| 9 | `AX_PeriodLattice` | full-rank period lattice | Mumford II§2 |
| 10 | `instPeriodLatticeDiscrete` | discreteness of period lattice | follows from #9 + Riemann bilinear |
| 11 | `AX_BranchLocus` | common fiber degree | Forster I§4 |
| 12 | `localOrder` | local multiplicity (well-defined) | Standard |

All 12 are well-formulated (right hypotheses; non-vacuous; load-bearing).

### A-construction (repo-specific construction-interface axioms):

Not classical theorems, but **engineering axioms** that move the
construction burden below the Buzzard API. Legitimate — each encodes
a well-defined classical function and each has a discharge plan — but
they should be named distinctly from classical-theorem axioms.

1. `pathIntegralBasepointFunctional` — function-existence axiom.
2. `loopIntegralToH1` — function-existence axiom.
3. `pullbackOneForm` — function-existence axiom.
4. `pushforwardOneForm` — function-existence axiom.
5. `localOrder` — function-existence axiom.
6. `AX_pathIntegral_local_antiderivative` — property of #1, links it to the form cocycle.
7. `AX_pullbackOneForm_id/_comp` — functoriality of #3.
8. `AX_pushforwardOneForm_id/_comp` — functoriality of #4.
9. `AX_pushforwardAmbient_preserves_lattice` — lattice-preservation for pushforward derived from #3.
10. `AX_pullbackAmbient_preserves_lattice` — same for pullback / #4.

All ten are cited in [`docs/construction-plans/`](construction-plans/)
with explicit discharge roadmaps.

### A-infra (non-classical, technical infrastructure gap):

**None** (as of 2026-04-23 round-3 refactor). `AX_jacobian_lieAddGroup`
was closed via Path A — proving the two ULift-smoothness lemmas
`contMDiff_ulift_up` / `contMDiff_ulift_down` inline.

### A-test (axioms used only by extension/test theorems, not foundation):

| # | Axiom | Statement | Used by |
|---|---|---|---|
| T1 | `AX_Liouville_compact_complex_manifold` | analytic `f : M → ℂ` on compact connected complex manifold ⇒ `f` constant | `AX_HyperellipticForm_polynomial_decomposition` (Level 2) |
| T2 | `AX_HyperellipticForm_polynomial_decomposition` | every holomorphic 1-form on `HyperellipticEvenProj H` has chart-local representation `g(z)/y(z)` for `g.natDegree < N/2 - 1` | `AX_HyperellipticOneForm_eq_form` (Level 3) |
| T3 | `AX_HyperellipticOneForm_eq_form` | every holomorphic 1-form on `HyperellipticEvenProj H` equals `hyperellipticForm H g` for some low-degree `g` | `genus_HyperellipticEven_le` (real theorem) |
| T4 | `hyperellipticEvenCoeff_cocycle_inl_inr_axiom` | cross-summand cocycle equation, `inl_inr` direction (under gluing hypothesis) | `_satisfiesCotangentCocycle` bundling |
| T5 | `hyperellipticEvenCoeff_cocycle_inr_inl_axiom` | cross-summand cocycle equation, `inr_inl` direction (under gluing hypothesis) | `_satisfiesCotangentCocycle` bundling |

T1–T3 form the layered Liouville hierarchy. T1 is a statement about
arbitrary compact complex manifolds (no project-specific defs); discharge
needs Mathlib's not-yet-fully-assembled chart-local maximum modulus
plus a connectedness-gluing argument. T2 derives from T1 + growth bounds
at infinity. T3 derives from T2 + the cocycle (real for `inl_inr`
under low-degree, modulo the soundness fix on T4).

T4 is **also available as a real theorem** under
`g_aff.natDegree < N/2 - 1` (`hyperellipticEvenCoeff_cocycle_inl_inr`);
the axiom remains in the bundling step until task #21 plumbs `hDeg`
through `hyperellipticForm`.

T5 still requires a real proof — symmetric structure to T4 with the
chart-transition derivative-product-to-1 swap.

A-test axioms are **soundness-gated by task #21** (T4 high-degree
unsoundness) but no foundation theorem is exposed to that gap; only
`genus_HyperellipticEven_eq` and the Liouville-hierarchy chain land
on these.

---

## Verdict

**Every F-class and H-class foundation definition is closed** under the
rule "real def OR properly-formulated axiom with discharge plan OR
textbook-citable classical theorem":

- ✓ §§1–13, §16 all bottom out cleanly at R + A-deep + A-construction.
- ✓ §9 (`LieAddGroup`) closed as real instance via ULift-smoothness.

**Axiom classification** (honest breakdown per Codex 2026-04-23 review):

| Class | Count | Nature |
|---|---|---|
| A-deep (classical theorem, textbook-citable) | ~10 | FiniteDimOneForms, PeriodLattice (×2), BranchLocus, genus_eq_zero_iff_homeo, ofCurve_inj, pushforward_pullback, ofCurve_contMDiff, pushforward_contMDiff, pullback_contMDiff, + Axioms/{RiemannBilinear, RiemannRoch, SerreDuality, AbelTheorem, PluckerFormula, Uniformization0} |
| A-construction (repo-specific function-existence + their Prop companions) | 10 | See above list |
| A-curve-atlas (for Hyperelliptic/PlaneCurve, axiomatizing the atlas construction) | ~10 | Hyperelliptic{TopologicalSpace, T2Space, CompactSpace, ConnectedSpace, Nonempty, ChartedSpace, IsManifold}, ditto PlaneCurve; plus HyperellipticEven + its 5 instances |
| A-infra (non-classical technical gaps) | 0 | — |

**No honest foundation gap at the Buzzard API**: every Buzzard-exposed
definition and every instance on `Jacobian X` is a real Lean `def` /
`instance`. The axiomatization is the sum of classical-theorem,
construction-interface, and atlas-construction axioms — each
well-formulated and discharge-planned.

**Hack-blocker caveat**: the hack-blocker argument (`ofCurve_inj`
forces genuine injectivity in positive genus, `genus_eq_zero_iff_homeo`
forces `genus` to track topology) is as strong as the axioms that
enforce it — `AX_ofCurve_inj`, `AX_genus_eq_zero_iff_homeo`,
`AX_genus_Elliptic_eq_one`, `AX_Hyperelliptic_genus`. A truly
independent defence of the blockers would require proving genus via
an explicit basis (e.g., `x^k dx / y` on hyperelliptic), which is a
separate project.

**Solid concrete witnesses**: `ProjectiveLine` (genus 0) and
`Elliptic ω₁ ω₂` (genus 1) are real `def`s with axiom-free topology
and manifold structure. `HyperellipticOdd H h` (odd `deg f`) is a
real `def` via `OnePoint (HyperellipticAffine H)` — the correct model
for the odd-degree case. Even-degree hyperelliptic curves and plane
curves of degree ≥ 2 stay axiom-stubbed pending the atlas work.

## Related documents

- `docs/challenge-annotated.md` — F/T classification of Buzzard's 24 sorries.
- `docs/challenge-summary.md` — Zulip-anchored context.
- `docs/completion-plan.md` — path to full discharge.
- `docs/hyperelliptic-atlas-plan.md` — 6-phase Hyperelliptic atlas plan.
- `docs/definitions-completion-plan.md` — scope choices for today's session.
