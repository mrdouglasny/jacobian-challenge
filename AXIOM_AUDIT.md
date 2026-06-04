# Axiom audit — jacobian-challenge

*Last updated 2026-06-04.*

In this project an **axiom** is a staging point: a statement we use before
its Lean proof is assembled, with the trust boundary kept explicit and the
discharge tracked. The goal is for every entry below to become a proved
theorem. Format conventions: [`~/.claude/AXIOM_AUDIT_FORMAT.md`]; deep
per-declaration trace: [`docs/dependency-trace.md`](docs/dependency-trace.md);
machine-checked dependency of every headline:
[`docs/axiom-report.txt`](docs/axiom-report.txt).

**Active project axioms: 66** — **64** in our modules + **2** vendored Kirov
`:= sorry` declarations restated as named axioms. (Verified against the
kernel, not a text scan — see [Verification](#verification). A text scan of
`^axiom ` also reports 64 once the 9 doc-comment example lines tagged
`-- not-an-axiom` are excluded.) History: 95 → 93 when task #21 retired the two
unsound cocycle axioms (2026-06-01); → 94 with the `AX_curve_generates_jacobian`
universal-property stub (2026-06-02, unused — see the Universal-property section);
→ 93 when `localOrder` was discharged to a real `def` via the adopted Wallace
`HolomorphicMap` module (2026-06-03); → 90 when `pullbackOneForm` and its
identity/composition laws were transported through Kirov's pullback
(2026-06-03); → 86 with Phase 1 — the Divisor cluster
(`Divisor`/`instAddCommGroup`/`deg` → `FreeAbelianGroup`) and `AX_BranchLocus` → theorem
(2026-06-04); → 82 with the Phase 2 accept-leaf cluster — 4 unified-`Hyperelliptic`
instances (`instCompactSpace`/`instConnectedSpace`/`instT2Space`/`instNonempty`)
discharged by parity dispatch through the `≃ₜ` equiv axioms (2026-06-04); → 76 with
the **full 6-axiom bridgePath cluster** (`bridgePath` def +
`_continuous`/`_chart_differentiable`/`_at_zero`/`_at_one`/`_lineIntegrable`)
discharged via the new `Bridge/BridgePath.lean` smooth-path-connectedness
infrastructure (a connected complex 1-manifold is smoothly path-connected:
flat-endpoint reparametrisation + chart-ball subdivision + smooth concatenation,
~1450 LOC; `_lineIntegrable` from continuity of `Vendor.Kirov.pathSpeed` ⇒
`IntervalIntegrable`) (2026-06-04); → 66 with the **Phase-3 prerequisite-type
discharges** (2026-06-04): the unified `Hyperelliptic` type became a real
parity-dispatch `def` cascading to `instTopologicalSpace`/`instChartedSpace`/
`instIsManifold` + `oddEquiv`/`evenEquiv` (6); `infinityInverseMap` (1); and
`PlaneCurve` became a faithful `Projectivization`-subtype `def` cascading to
`instTopologicalSpace`/`instNonempty` (3). The sheaf-cohomology faithfulness
suite [`SheafCohomologySpec.lean`](Jacobians/RiemannSurface/SheafCohomologySpec.lean)
was added as the machine-checkable acceptance gate for the (still-axiomatized)
`H0`/`H1`/`LineBundle` cluster — see [`docs/planning/PHASE_3_INFRA_PLAN.md`](docs/planning/PHASE_3_INFRA_PLAN.md).

---

## Triage

Per the review plan, axioms are split into two classes:

- **Class 1 — standard form, textbook-proven** (14 axioms). Statements are
  the standard textbook ones, citable, with no ambiguity about their form;
  discharging them is "port the textbook proof / wait for Mathlib." These
  are the *trusted* axioms.
- **Class 2 — form or proof not yet clear** (52 axioms). Either the Lean
  encoding is a project-specific stub whose faithfulness needs checking, or
  the statement asserts good behaviour of one of our constructions (and
  could mask a bad definition), or it is a large atlas/analysis fact with no
  obvious discharge. **This is the class to focus on.** Subdivided 2a–2d
  below, with 2d (Flagged) the most urgent.

| Class | Count | Nature | Trust |
|------|------:|--------|-------|
| 1 — textbook-standard | 14 | classical theorems, citable | high |
| 2a — data-existence | 16 | "this function/object exists with spec S" | spec needs review |
| 2b — definition-asserting | 9 | "my construction has good property P" | **may mask a bad def** |
| 2c — atlas / structure | 25 | curve-specific chart constructions | real but unverified |
| 2d — **flagged** | 2 | true-but-unproven (Liouville L2/L3) | needs end-to-end check |

---

## Class 1 — standard form, textbook-proven

Rating **Standard**; sources `SA` (self-audit vs textbook) + `GR`/`DT`
(Gemini review, 2026-04-22/23/29 per commit history) where noted.

| Axiom | File:Line | Reference |
|-------|-----------|-----------|
| `AX_RiemannRoch` | `Axioms/RiemannRoch.lean:59` | Forster §16; Miranda Ch. VI |
| `AX_SerreDuality` | `Axioms/SerreDuality.lean:54` | Forster §17; Griffiths–Harris Ch. 1 |
| `AX_RiemannBilinear` | `Axioms/RiemannBilinear.lean:69` | Griffiths–Harris Ch. 2 (bilinear relations) |
| `AX_AbelTheorem` | `Axioms/AbelTheorem.lean:66` | Forster §21; Miranda Ch. VIII |
| `AX_PluckerFormula` | `Axioms/PluckerFormula.lean:55` | Griffiths–Harris Ch. 2 (Plücker) |
| `AX_genus_eq_zero_iff_homeo` | `Axioms/Uniformization0.lean:55` | uniformization, genus 0 (Forster §27) |
| `AX_AnalyticCycleBasis` | `Axioms/AnalyticCycleBasis.lean:257` | symplectic H₁ basis (standard) |
| `AX_IntersectionForm_alternating` | `Axioms/IntersectionForm.lean:66` | cup product on H₁ (standard) |
| `AX_IntersectionForm_perfect` | `Axioms/IntersectionForm.lean:91` | Poincaré duality / unimodularity |
| `AX_PeriodLattice` | `Axioms/PeriodLattice.lean:92` | period lattice is a full ℤ-lattice |
| `instPeriodLatticeDiscrete` | `Axioms/PeriodLattice.lean:77` | discreteness of the period lattice |
| `AX_curve_generates_jacobian` | `Axioms/UniversalProperty.lean:44` | Mumford *Curves & their Jacobians*; Milne *AV* §I — *unused stub* (see Universal-property section) |
| `Vendor.Kirov…genus_eq_zero_iff_homeo` | `Vendor/Kirov/Genus.lean:94` | uniformization (Kirov handoff) |
| `Vendor.Kirov…ambientPhi_ambientPsi_eq` | `Vendor/Kirov/HolomorphicForms.lean:340` | degree identity (Kirov handoff) |

*Note.* `AX_genus_eq_zero_iff_homeo` is still an axiom **only** for the
abstract `genus_eq_zero_iff_homeo`; the concrete `genus ℙ¹ = 0` no longer
uses it (proven directly — see Recently discharged).

---

## Class 2 — form or proof not yet clear  *(the focus)*

### 2a. Data-existence axioms — *the spec is the question*

"This function/object exists satisfying spec S." Risk: the spec is vacuous
or contradictory, or doesn't pin down the intended object. The three marked
🅒 have written construction plans in
[`docs/construction-plans/`](docs/construction-plans/).

| Axiom | File:Line | Note |
|-------|-----------|------|
| `pathIntegralBasepointFunctional` 🅒 | `Axioms/AbelJacobiMap.lean:96` | the path-integral functional; **opaque** (see `ofCurve` card) |
| `AX_pathIntegral_local_antiderivative` | `Axioms/AbelJacobiMap.lean:114` | chart-local FTC binding the functional to the cocycle |
| `loopIntegralToH1` 🅒 | `RiemannSurface/PathIntegral.lean:101` | H₁-level period descent |
| `pushforwardOneForm` 🅒 | `Axioms/AbelJacobiMap.lean:143` | trace of 1-forms |
| `intersectionForm` | `Axioms/IntersectionForm.lean:59` | the pairing itself (properties are Class 1) |
| `abelJacobiDiv` | `Axioms/AbelTheorem.lean:60` | divisor-level Abel–Jacobi |
| `PrincipalDivisors`, `LineBundle`, `H0`(+`instAddCommGroup`,`instModule`), `H1`(+`instAddCommGroup`,`instModule`), `canonicalDivisor`, `LineBundle.ofDivisor` (10) | `RiemannSurface/LineBundle.lean:70–128` | line-bundle / sheaf-cohomology **type stubs** (the `Divisor` triple discharged in Phase 1) |

### 2b. Definition-asserting axioms — *may mask a bad definition*

"My construction behaves correctly." These are the disguised risk: each
could be papering over a degenerate definition. Validation = discharge on a
concrete witness (see [`docs/validation-plan.md`](docs/validation-plan.md) §C).

| Axiom | File:Line | Note |
|-------|-----------|------|
| `AX_ofCurve_inj` | `Axioms/AbelJacobiMap.lean:245` | Buzzard's anti-`J=0` hack-blocker; **opaque-blocked** (see [`docs/contracts/ofCurve.md`](docs/contracts/ofCurve.md)) |
| `AX_ofCurve_contMDiff` | `Axioms/AbelJacobiMap.lean:226` | Abel–Jacobi smoothness |
| `AX_pushforward_contMDiff` | `Axioms/AbelJacobiMap.lean:570` | pushforward smoothness |
| `AX_pullback_contMDiff` | `Axioms/AbelJacobiMap.lean:619` | pullback smoothness |
| `AX_pushforward_pullback` | `Axioms/AbelJacobiMap.lean:667` | push∘pull = deg multiplication |
| `AX_pushforwardAmbient_preserves_lattice` | `Axioms/AbelJacobiMap.lean:298` | period-map naturality |
| `AX_pullbackAmbient_preserves_lattice` | `Axioms/AbelJacobiMap.lean:312` | period-map naturality |
| `AX_pushforwardOneForm_id` / `_comp` | `Axioms/AbelJacobiMap.lean:178,185` | functoriality of trace |

### 2c. Atlas / structure axioms — *curve-specific constructions*

Real chart/manifold constructions for specific curves; classically true,
discharge is substantial chart work. As of the Phase-3 batch (2026-06-04) the
unified `Hyperelliptic` and `PlaneCurve` *types* are now real `def`s; what
remains here is their **atlas/manifold** instances + the genus formula.

| Cluster | File:Lines | Count |
|---------|-----------|------:|
| `AX_Hyperelliptic_genus` only (type + `instTopologicalSpace`/`instChartedSpace`/`instIsManifold` + `oddEquiv`/`evenEquiv` discharged Phase-3; genus needs biholo, not just homeo) | `ProjectiveCurve/Hyperelliptic.lean` | 1 |
| `PlaneCurve`: 5 manifold/topology instances (`instT2Space`/`instCompactSpace`/`instConnectedSpace`/`instChartedSpace`/`instIsManifold`) + 3 affine props (type + `instTopologicalSpace`/`instNonempty` discharged Phase-3 Tier-1) | `ProjectiveCurve/PlaneCurve.lean` | 8 |
| Odd-atlas infinity chart (`infinityChart`, 4 compat, `mem_source`; `infinityInverseMap` discharged Phase-3) | `…/OddAtlas/InfinityChart.lean` | 6 |
| Even-atlas compatibility (`affineLiftChart_compat_…`, `…_compat_…`) | `…/Hyperelliptic/EvenAtlas.lean:243,252` | 2 |
| Affine-form IFT-shape (`squareLocalHomeomorph_zero_notMem_source`, `polynomialLocalHomeomorph_no_critical_in_source`) | `…/Hyperelliptic/AffineForm.lean:66,222` | 2 |
| `AX_HyperellipticAffine_connected` | `…/Hyperelliptic/Basic.lean:101` | 1 |
| `contDiffOn_symm_toOpenPartialHomeomorph` (narrow IFT gap) | `GeneralResults/InverseFunctionTheorem.lean:9` | 1 |
| Elliptic witnesses (`AX_Elliptic_aLoop_analytic`, `_bLoop_analytic`, `_H1_symplectic`) | `…/Elliptic/Witnesses.lean:86,90,166` | 3 |
| `AX_H1_ProjectiveLine_trivial` | `…/Line/Witnesses.lean:43` | 1 |

### 2d. Flagged — *true-but-unproven; needs end-to-end check*

The two cross-summand cocycle axioms that used to live here were **unsound**
(false for `deg g ≥ N/2−1`) and are now **retired** — see Recently
discharged. The remaining two are the Liouville hierarchy L2/L3 — genuinely true,
but not yet checked end-to-end. They are the classical canonical-differentials
theorem for hyperelliptic curves (the deepest result left); L3 is shown to
reduce to L2 + cocycle propagation (`hyperellipticForm_coeff_projX`), and L2
is decomposed in [`docs/genus-L2-L3-discharge-plan.md`](docs/genus-L2-L3-discharge-plan.md)
(L2-step-4 already proven; the branch-point + degree-at-∞ core remains, ~1–2 months).

| Axiom | File:Line | Status |
|-------|-----------|--------|
| `AX_HyperellipticForm_polynomial_decomposition` (Liouville L2) | `Axioms/HyperellipticLiouville.lean:215` | true-but-unproven. **Step 4 of its proof plan is proven** (`differentiable_eq_polynomial_of_growth`); steps 1–3 (branch-point regularity + degree-at-∞) remain. |
| `AX_HyperellipticOneForm_eq_form` (Liouville L3) | `Axioms/HyperellipticLiouville.lean:260` | true-but-unproven. Surjectivity of `hyperellipticForm` onto the low-degree forms; feeds `genus_HyperellipticEven_le`. **Reduces to L2 + cocycle propagation** (`hyperellipticForm_coeff_projX`, the bridge lemma). The only remaining gap in the even-genus theorem. |

---

## Universal-property axioms (discharge plan)

Deferred textbook leaves of [`docs/universal-property-proof-plan.md`] (proving
`Jacobians.IsJacobian x₀ (Jacobian X) (ofCurve x₀)` — the categoricity theorem).
All cross-model vetted **Gemini (gemini-3-pro-preview) + Codex, 2026-06-02**
(`GR`+`CX`); ratings **Standard**/**Likely correct**. None is yet used by a
theorem (so the headline-reachable axiom set is unchanged); they are forward debt.

| Axiom | Status | Reference |
|-------|--------|-----------|
| `AX_curve_generates_jacobian` | **stated** — `Axioms/UniversalProperty.lean:44` (compiles; unused stub, +1 to the declared count) | Mumford; Milne *AV* §I |
| `AX_torus_oneforms_dualCover` | **planned** — Lean form pending complex-torus 1-form ≅ cotangent API (Codex: Mathlib has `GroupLieAlgebra`/`addInvariantVectorField` scaffolding; the equiv is absent) | Birkenhake–Lange Ch. 1 |
| `AX_torus_self_albanese` | **planned** — pending a torus-Albanese object | Birkenhake–Lange Ch. 1 |
| `AX_period_functoriality` | **planned** — pending the singular/de-Rham period pairing + naturality (Codex: `curveIntegral` + `singularHomologyFunctor` exist; pairing absent) | Griffiths–Harris Ch. 0 & 2 |

The holomorphicity step (E6 in the plan) is **likely provable** from Mathlib
(`LinearMap.toContinuousLinearMap` + `ZLatticeQuotient`), not axiomatized; the
"every abstract torus hom is holomorphic" form is *false* (Codex-flagged) — use the
ℂ-linear-lift form only. Step 0 (the `ConnectedSpace (Jacobian X)` instance needed
for the goal to typecheck) is **done** (`Jacobian/Construction.lean`,
`Challenge.lean`).

## Recently discharged (now axiom-free)

| Was axiom | Discharged via | Proof lives in |
|-----------|----------------|----------------|
| `AX_FiniteDimOneForms` | injective bridge to Kirov's Montel theorem | `Bridge/KirovHolomorphic.lean` |
| `genus ℙ¹ = 0` *(via `AX_genus_eq_zero_iff_homeo`)* | direct chart-cocycle + Liouville ⇒ `HolomorphicOneForm ℙ¹` subsingleton | `ProjectiveCurve/Line/OneForm.lean` |
| `AX_Liouville_compact_complex_manifold` (Liouville L1) | global max-modulus (`Complex.eqOn_…isMaxOn_norm`) + clopen connectedness | `Axioms/HyperellipticLiouville.lean` (`liouville_compact_complex_manifold`) |
| Liouville L2 **step 4** (growth ⇒ polynomial) | induction + Liouville + `dslope` | `GeneralResults/EntireGrowth.lean` (`differentiable_eq_polynomial_of_growth`) |
| `hyperellipticEvenCoeff_cocycle_inl_inr_axiom` *(was UNSOUND)* | real low-degree proof (S5 sub-cases) | `EvenForm.lean` (`…_cocycle_inl_inr`) |
| `hyperellipticEvenCoeff_cocycle_inr_inl_axiom` *(was UNSOUND)* | chart-transition symmetry from `inl_inr` | `EvenForm.lean` (`…_cocycle_inr_inl`) + `GeneralResults/ChartTransition.lean` |
| `localOrder` *(2026-06-03)* | real `def` = `if f p = q then mapAnalyticOrderAt f p else 0`, using the adopted Wallace `HolomorphicMap` (`analyticOrderNatAt`); **faithfulness witness** `localOrder_pow` proves `localOrder (z↦zᵏ) 0 0 = k` (`#print axioms` ⊆ the 3 standard) | `Axioms/BranchLocus.lean` (`def` + `localOrder_pow`) |
| `pullbackOneForm`; `AX_pullbackOneForm_id` / `_comp` *(2026-06-03)* | transported across `bridgeFormEquiv` from Kirov's real `pullbackForm`, `pullbackForm_id`, and `pullbackForm_comp` (`#print axioms` = standard 3) | `Bridge/KirovHolomorphicEquiv.lean` + `Axioms/AbelJacobiMap.lean` |
| `Divisor`; `Divisor.instAddCommGroup`; `Divisor.deg` *(Phase 1, 2026-06-04)* | `abbrev Divisor X := FreeAbelianGroup X`; `AddCommGroup` via `inferInstanceAs`; `deg := FreeAbelianGroup.lift (fun _ => 1)`. Unblocks the 11 downstream sheaf-cohomology plans | `RiemannSurface/LineBundle.lean` |
| `AX_BranchLocus` *(Phase 1, 2026-06-04)* | `theorem` wiring Wallace `weightedFiberConservation_of_contMDiff` → local-to-global constancy (`LocallyConstant`) → `tsum` fiber-degree + finite branch locus via finite subcover (`#print axioms` = standard 3; vendored unmodified) | `Axioms/BranchLocus.lean` |
| `Hyperelliptic.{instCompactSpace,instConnectedSpace,instT2Space,instNonempty}` *(Phase 2, 2026-06-04)* | `instance`s by parity dispatch through `AX_Hyperelliptic_oddEquiv`/`evenEquiv`: `.symm.compactSpace`/`.symm.t2Space`, `.connectedSpace_iff.mpr inferInstance`, `Nonempty.map .symm inferInstance` | `ProjectiveCurve/Hyperelliptic.lean` |
| **bridgePath cluster — all 6**: `bridgePath`, `bridgePath_continuous`, `bridgePath_chart_differentiable`, `bridgePath_at_zero`, `bridgePath_at_one`, `bridgePath_lineIntegrable` *(2026-06-04)* | new `BridgePath.lean` proves a connected complex 1-manifold is smoothly path-connected: `bridgePathImpl` = chart-ball Lebesgue subdivision of a `PathConnectedSpace` path, replaced piecewise by flat-endpoint affine segments (`flatSegment`, `flatReparam`) concatenated via `Path.trans`; `_continuous` from `Path.continuous_extend`, endpoints `@[simp]`, `_chart_differentiable` from the recentring chart-transition (`contDiffWithinAt_ext_coord_change` ⇒ `DifferentiableAt.restrictScalars`) + per-piece interior + dyadic junction glue (`HasDerivWithinAt.union`). `bridgePath` becomes a `def`, the rest theorems backing the same names. `_lineIntegrable` then follows from continuity of `Vendor.Kirov.pathSpeed (bridgePath …)` ⇒ `IntervalIntegrable` (`#print axioms` = standard 3; `lake build Jacobians` green, no downstream fallout) | `Bridge/BridgePath.lean` + `Bridge/KirovLineIntegral.lean` |
| **Hyperelliptic type cascade** (6): `Hyperelliptic`, `instTopologicalSpace`, `instChartedSpace`, `instIsManifold`, `AX_Hyperelliptic_oddEquiv`, `AX_Hyperelliptic_evenEquiv` *(Phase 3, 2026-06-04)* | `Hyperelliptic` → `noncomputable def` by parity dispatch `if h : Odd … then HyperellipticOdd H h else HyperellipticEvenProj H`; the 3 data instances derive by case-split + `dif_pos/neg` (even branch via `Fact (¬Odd)`); the equivs become `Homeomorph`s from the type equality. Explicit instances match the head symbol, so the dite did not trip downstream typeclass synthesis. `#print axioms` = standard 3 | `ProjectiveCurve/Hyperelliptic.lean` |
| `infinityInverseMap` *(Phase 3, 2026-06-04)* | real `def` for the odd-atlas inverse coordinate map at infinity | `…/OddAtlas/InfinityChart.lean` |
| **PlaneCurve Tier-1** (3): `PlaneCurve`, `instTopologicalSpace`, `instNonempty` *(Phase 3, 2026-06-04)* | `PlaneCurve` → faithful subtype `def` of `Projectivization ℂ (Fin 3 → ℂ)` via an existential-representative predicate (`∃ v hv, mk v hv = p ∧ eval v = 0`, rep-independent using `H.F.homogeneous`); topology from the subtype, nonempty from a projective solution. `instT2Space/instCompactSpace/instConnectedSpace` left as honest axioms (no synthesized `Projectivization` compact/T2 package in this pin). `#print axioms` = standard 3 | `ProjectiveCurve/PlaneCurve.lean` |

The two cocycle axioms (task #21, 2026-06-01) were the only **unsound**
axioms in the repo; their retirement makes `genus_HyperellipticEven_eq`
sound modulo the (true-but-unproven) Liouville L2/L3. `hyperellipticForm`
is now total-but-axiom-free (zero form above degree `N/2−1`), with its
linear-algebra API on `Polynomial.degreeLT ℂ (N/2−1)`.

All verified core-axioms-only via `#print axioms`.

---

## Related audit artifacts

- [`docs/dependency-trace.md`](docs/dependency-trace.md) — per-Buzzard-declaration transitive axiom trace + classical references.
- [`docs/contracts/`](docs/contracts/) — per-object contract cards (`genus`, `ofCurve`): judge a construction without reading its proof; the `known_values` tables tie axioms to concrete witnesses.
- [`docs/validation-plan.md`](docs/validation-plan.md) — how to validate each class (non-vacuity sentinels for 2a, concrete-witness discharge for 2b, faithful-encoding review for Class 1).
- [`docs/axiom-report.txt`](docs/axiom-report.txt) — golden `#print axioms` of every headline (regenerate with [`scripts/axiom_report.lean`](scripts/axiom_report.lean)); guards against `sorryAx` creep.

---

## Verification

The text scan over-counts (doc examples); the kernel is authoritative.

```bash
# kernel count of project axioms (excludes Lean-core + compiler-internal axioms + Vendor)
#   prints 80; add the 2 Vendor/Kirov axioms for the total 82.
lake env lean <<'LEAN'
import Jacobians
open Lean
run_cmd do
  let env ← getEnv
  let internal := [`propext, `Classical.choice, `Quot.sound, `sorryAx, `lcProof,
    `lcCast, `lcErased, `lcAny, `lcUnreachable, `lcVoid, `Quot.lcInv, `isScalarObj,
    `Lean.ofReduceBool, `Lean.ofReduceNat, `Lean.trustCompiler]
  let mut n := 0
  for (nm, info) in env.constants.toList do
    if info matches .axiomInfo _ then
      let s := nm.toString
      if !s.startsWith "Jacobians.Vendor" && !(internal.contains nm) then n := n + 1
  logInfo s!"project axioms (non-vendor): {n}"
LEAN

# text cross-check (9 doc-example lines are tagged `-- not-an-axiom`):
grep -rnE '^axiom ' Jacobians --include='*.lean' | grep -v '/Vendor/' | grep -v 'not-an-axiom' | wc -l
```
