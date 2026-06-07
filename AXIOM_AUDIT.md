# Axiom audit — jacobian-challenge

*Last updated 2026-06-07.*

In this project an **axiom** is a staging point: a statement we use before
its Lean proof is assembled, with the trust boundary kept explicit and the
discharge tracked. The goal is for every entry below to become a proved
theorem. Format conventions: [`~/.claude/AXIOM_AUDIT_FORMAT.md`]; deep
per-declaration trace: [`docs/dependency-trace.md`](docs/dependency-trace.md);
machine-checked dependency of every headline:
[`docs/axiom-report.txt`](docs/axiom-report.txt).

**Active project axioms: 49** — all **49** in our own modules. The vendored
Kirov subtree is now **axiom-free**: its 2 unused `:= sorry`-handoff axioms
(`genus_eq_zero_iff_homeo`, `ambientPhi_ambientPsi_eq`) were deleted 2026-06-04
(they had no references beyond their own declarations; the challenge uses the
main-tree `AX_genus_eq_zero_iff_homeo`), matching the axiom-free Wallace vendor.
(Verified against the
kernel, not a text scan — see [Verification](#verification).) History: 95 → 93 when task #21 retired the two
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
discharges** (2026-06-04, → 68 after the corrective review below): the unified
`Hyperelliptic` type became a real parity-dispatch `def` cascading to
`instTopologicalSpace`/`instChartedSpace`/`instIsManifold` + `oddEquiv`/`evenEquiv`
(6 — the **carrier is standard-3** via a `Decidable.casesOn`-motive parity
dispatch; only `instChartedSpace`/`instIsManifold` transport the sound,
unproven odd-`infinityChart` + even-atlas axioms, where that dependency belongs;
no NEW axioms introduced); and `PlaneCurve` became a faithful
`Projectivization`-subtype `def` cascading to `instTopologicalSpace` (2). The
sheaf-cohomology faithfulness
suite [`SheafCohomologySpec.lean`](Jacobians/RiemannSurface/SheafCohomologySpec.lean)
was added as the machine-checkable acceptance gate for the (still-axiomatized)
`H0`/`H1`/`LineBundle` cluster — see [`docs/planning/PHASE_3_INFRA_PLAN.md`](docs/planning/PHASE_3_INFRA_PLAN.md).
**Corrective review (2026-06-04, → 68):** kernel-checking the discharges surfaced
three problems (reviewer-found). `infinityInverseMap` was reverted (its `def`
picked an *arbitrary* polynomial root, not the analytic branch at infinity) and
`PlaneCurve.instNonempty` was reverted (it proved nonemptiness via the
*false* `AX_PlaneCurveAffine_nonempty`) — both back to honest axioms (+2). The
`PlaneCurveAffine` axiom layer was made sound by strengthening `PlaneCurveData`
(`h_irreducible` + `z ∤ F`). And the `Hyperelliptic` carrier was **unbundled**
(pure `Decidable.casesOn` parity dispatch) so `#print axioms Hyperelliptic` is
now genuinely standard-3 — the atlas dependency lives only in the chart/manifold
instances. → **66** by deleting the 2 unused vendored Kirov handoff
axioms (`genus_eq_zero_iff_homeo`, `ambientPhi_ambientPsi_eq`), leaving the
vendored subtree axiom-free. → **65** by deleting the **false** dangling
axiom `AX_pathIntegral_local_antiderivative` (the single-valued ℂ "FTC" for the
period functional): on any genus ≥ 1 curve it forces a global primitive of a
holomorphic 1-form, hence zero periods — contradicting `genus_Elliptic = 1`. It
was unused (0 headline dependents), an unsoundness landmine; the honest
path-independence content lives at the homology level in `loopIntegralToH1`, and
a genuine FTC can only be stated on the quotient `ofCurve : X → ℂ^g/Λ`. Finally →
**64** by **de-opaquing** `pathIntegralBasepointFunctional` from an axiom to a
real `def` (`:= Bridge.kirovBackedFunctional`, itself standard-3 axiom-clean): a
genuine line integral `∫_{bridgePath P₀ P}`. `ofCurve` is now a **computed** map;
the zero-functional degeneracy it hid is gone (2026-06-04). Finally, **`loopIntegralToH1`
— the path-independence axiom — was DISCHARGED to a real `def` 2026-06-05** (count
stays 64: −`loopIntegralToH1`, +the then-axiomatized
`AX_cycleBasisLoop_integrable`): the period pairing
is now `cb.isBasis.constr ℤ (∮ over the analytic cycle-basis loops)`, the integrals
being the genuine L0–L1 multi-chart integral (chart-cocycle + partition-independence
all **proven**, ~10 new modules). `periodMap`/`ofCurve` no longer list
`loopIntegralToH1`; they rest on `AX_AnalyticCycleBasis` + `intersectionForm` (the
symplectic cycle basis, already needed for the lattice) + the then-trivial
integrability axiom, now proved — see Recently discharged. **Basis-faithfulness
(PR #7 review fix):** the
`AnalyticCycleBasis` structure gained a `loops_to_basis` field
(`∀ i, isBasis i = loopToHomology (loops i)`, the Hurewicz loop→class tie) —
honestly strengthening `AX_AnalyticCycleBasis`/`AX_Elliptic_H1_symplectic`, no new
axiom — so `loopIntegralToH1_loop` proves `loopIntegralToH1 (loopToHomology (cb.loops i))
= ∮_{cb.loops i}`: the pairing assigns each basis loop's **genuine period** to its
H₁ class. The deepest analytic gap is closed; only full homotopy invariance
(representative-independence for *arbitrary* loops, not just the basis) remains as a
deferred faithfulness upgrade.

Then → **63** by **de-opaquing** `abelJacobiDiv` from an axiom to a real `def`
(`:= FreeAbelianGroup.lift (fun P => ofCurveImpl X (Classical.arbitrary X) P)`, 2026-06-05):
the divisor-level Abel–Jacobi map is now the genuine linear extension of `ofCurveImpl`.
`AX_AbelTheorem` (kernel = principal divisors) stays the textbook axiom, now stated about
the concrete map. This is one input to the now-derived general `AX_ofCurve_inj`
(Abel injectivity, genus > 0) — see
[`docs/planning/OFCURVE_INJ_DISCHARGE_PLAN.md`](docs/planning/OFCURVE_INJ_DISCHARGE_PLAN.md).
Then → **62** by **de-opaquing** `PrincipalDivisors` to the additive subgroup
corresponding to `MeromorphicFunctionField.divHom.range` via `Subgroup.toAddSubgroup'`
(2026-06-05). No new axiom was introduced.

**Faithfulness fix (2026-06-05, count unchanged at 62).** Statement-vetting (Gemini
deep-think + self-audit) caught that, once `PrincipalDivisors` became the concrete
`range divHom` (all degree-0), the bare-kernel form `ker abelJacobiDiv = PrincipalDivisors`
is **false**: `abelJacobiDiv` sends the basepoint divisor `(arbitrary)` to `0`
(`AX_ofCurve_self`), so that degree-1 divisor lies in the kernel but is not principal —
a latent inconsistency (would become derivable once `deg(div f) = 0` lands). Fixed by
restricting to degree-0 divisors, matching Abel's actual theorem `Div⁰/Principal ≃ Jac`
and the axiom's own docstring:
`(abelJacobiDiv X).ker ⊓ (Divisor.deg X).ker = PrincipalDivisors X`. All consumers feed
only degree-0 divisors (differences `(Q₁)−(Q₂)`), so nothing is lost; the elliptic
witness does not depend on this axiom.

Then → **66** with the universal-property UP-0/UP-1 banked in
`Axioms/TorusAlbanese.lean` (2026-06-05): `AX_torus_oneforms_dualCover`,
`AX_torus_self_albanese`, `AX_period_functoriality`, and the conditional lift-form
fallback `AX_torus_descent_holo` used for E6. The pre-existing
`AX_curve_generates_jacobian` was moved into the new file, so it is not a net-new
axiom. Then → **63** by **de-opaquing** `H0` to the concrete
`riemannRochSpace D` and replacing `H0.instAddCommGroup` / `H0.instModule` with
instances inherited from the submodule carrier (2026-06-05). `LineBundle` and
`LineBundle.ofDivisor` remain honest opaque placeholders; `H1` remains opaque.
**Faithfulness correction (2026-06-06, count unchanged):** `riemannRochSpace` was
first defined over raw `X → ℂ`, which was *degenerate* — germ-zero "spike"
functions made it infinite-dimensional (`finrank ≡ 0`). It is now a submodule of
the **meromorphic germ quotient** `MeroField = MeroFunctions ⧸ GermZero`
(`RiemannSurface/RiemannRochSpace.lean`), the genuine `L(D)`; `germZero_ne_bot`
compiles the spike witness. `H0` still `:= riemannRochSpace D` (instances adapt;
no axiom change). **`h0_zero` (h⁰(0)=1) is now PROVED axiom-free** over the corrected
space (normal-form honest representative + Liouville ⇒ `L(0) ≃ ℂ`, `#print
axioms`-clean, tracked in `docs/axiom-report.txt`) — the concrete check that the
fix gives the right dimension (it was false over the old degenerate space). Only
general `riemannRochSpace_finiteDimensional` and `h0_canonical` remain deferred.
Then → **62** by **discharging `AX_torus_descent_holo`** (2026-06-06): it is now a
real `theorem` in `Axioms/TorusAlbanese.lean`, proving the descended quotient map
is `ContMDiff ω` via the local-section route over Kirov's `ZLatticeQuotient`
local-homeomorphism API (`isLocalHomeomorph_mk` + `contDiffOn_symm_mk`), composed
with `P.fromQuot_holo`; two `ComplexTorus` chart lemmas were de-privatized to
support it. `#print axioms`-clean (standard-3 + the upstream period-lattice /
cycle-basis axioms; no `sorryAx`, no self-reference).
Then → **59** by **proving `AX_cycleBasisLoop_integrable`** (2026-06-06) from the
strengthened `AnalyticArc` regularity: strong cell witnesses give
interval-integrability of canonical moving-chart integrands, and cycle-basis
loop integrability is now a theorem.
Then → **58** by **proving `AX_Period_Triangle`** (2026-06-06): the triangle is
closed by conjugating it to the Jacobian's chosen basepoint, the analytic-loop
period vector lies in `periodLatticeInBasis` by the new
`loopDevValH1Hom = loopIntegralToH1` agreement over `AX_AnalyticCycleBasis`, and
the bridge path cancels against its reverse by the canonical-arc algebra.
`#print axioms AX_Period_Triangle` now lists only standard-3 +
`AX_AnalyticCycleBasis` + `intersectionForm`; no self-reference, no new axiom,
and no `sorryAx`.

Then → **56** by **discharging `AX_pushforward_contMDiff` and
`AX_pullback_contMDiff` to theorems** (PR #88, 2026-06-06): the pushforward /
pullback maps on Jacobians (the quotient-torus maps `V ⧸ Λ → W ⧸ Λ'` induced by
a linear `Φ`) are proved smooth via a chart-level engine — after `contMDiffAt_iff`
the chart composition equals the affine map `Φ + c₀` on a neighbourhood, smooth
because `Φ` is a continuous linear map. Both were class 2b (definition-asserting),
now removed.

Then → **55** by **proving `AX_Elliptic_aLoop_analytic`** (PR #86, 2026-06-06): the
elliptic a-loop is analytic, via the new `extChartAt_quotient_mk_line_analyticAt`
(the quotient chart `ℂ → ℂ ⧸ L` is analytic on a line through the origin). One of
the three class-2c Elliptic-witness axioms. Then → **54** by **proving
`AX_Elliptic_bLoop_analytic`** (2026-06-07) by the same quotient-chart line
analyticity argument; only `_H1_symplectic` remains.

Then → **53** by **proving `AX_PlaneCurveAffine_nonempty`** (2026-06-07): the
affine patch is nonempty from `exists_eval_eq_zero_of_not_isUnit_mvPolynomial`
applied to the dehomogenized affine polynomial. The remaining PlaneCurve cluster
has six projective instances plus two affine props.

Then → **52** by **proving `PlaneCurve.instT2Space`** (PR #94, 2026-06-07):
`PlaneCurve H` is a subtype of the projectivization quotient, and
`projectivization_t2Space` supplies the ambient `T2Space` inherited by the
subtype.

---

## Triage

Per the review plan, axioms are split into two classes:

- **Class 1 — standard form, textbook-proven** (15 axioms). Statements are
  the standard textbook ones, citable, with no ambiguity about their form;
  discharging them is "port the textbook proof / wait for Mathlib." These
  are the *trusted* axioms.
- **Class 2 — form or proof not yet clear** (37 axioms). Either the Lean
  encoding is a project-specific stub whose faithfulness needs checking, or
  the statement asserts good behaviour of one of our constructions (and
  could mask a bad definition), or it is a large atlas/analysis fact with no
  obvious discharge. **This is the class to focus on.** Subdivided 2a–2d
  below, with 2d (Flagged) the most urgent.

| Class | Count | Nature | Trust |
|------|------:|--------|-------|
| 1 — textbook-standard | 15 | classical theorems, citable | high |
| 2a — data-existence | 8 | "this function/object exists with spec S" | spec needs review |
| 2b — definition-asserting | 6 | "my construction has good property P" | **may mask a bad def** |
| 2c — atlas / structure | 20 | curve-specific chart constructions | real but unverified |
| 2d — **flagged** | 0 | both Liouville L2/L3 **DISCHARGED** (now theorems) | — |

---

## Class 1 — standard form, textbook-proven

Rating **Standard**; sources `SA` (self-audit vs textbook) + `GR`/`DT`
(Gemini review, 2026-04-22/23/29 per commit history) where noted.

| Axiom | File:Line | Reference |
|-------|-----------|-----------|
| `AX_RiemannRoch` | `Axioms/RiemannRoch.lean:59` | Forster §16; Miranda Ch. VI |
| `AX_SerreDuality` | `Axioms/SerreDuality.lean:54` | Forster §17; Griffiths–Harris Ch. 1 |
| `AX_RiemannBilinear` | `Axioms/RiemannBilinear.lean:69` | Griffiths–Harris Ch. 2 (bilinear relations) |
| `AX_AbelTheorem` | `Axioms/AbelTheorem.lean:80` | Forster §21; Miranda Ch. VIII (degree-0 restricted form) |
| `AX_PluckerFormula` | `Axioms/PluckerFormula.lean:55` | Griffiths–Harris Ch. 2 (Plücker) |
| `AX_genus_eq_zero_iff_homeo` | `Axioms/Uniformization0.lean:55` | uniformization, genus 0 (Forster §27) |
| `AX_AnalyticCycleBasis` | `Axioms/AnalyticCycleBasis.lean:257` | symplectic H₁ basis (standard) |
| `AX_IntersectionForm_alternating` | `Axioms/IntersectionForm.lean:66` | cup product on H₁ (standard) |
| `AX_IntersectionForm_perfect` | `Axioms/IntersectionForm.lean:91` | Poincaré duality / unimodularity |
| `AX_PeriodLattice` | `Axioms/PeriodLattice.lean:92` | period lattice is a full ℤ-lattice |
| `instPeriodLatticeDiscrete` | `Axioms/PeriodLattice.lean:77` | discreteness of the period lattice |
| `AX_torus_oneforms_dualCover` | `Axioms/TorusAlbanese.lean:73` | Birkenhake–Lange Ch. 1 |
| `AX_torus_self_albanese` | `Axioms/TorusAlbanese.lean:88` | Birkenhake–Lange Ch. 1 |
| `AX_period_functoriality` | `Axioms/TorusAlbanese.lean:120` | Griffiths–Harris Ch. 0 & 2 |
| `AX_curve_generates_jacobian` | `Axioms/TorusAlbanese.lean:168` | Mumford *Curves & their Jacobians*; Milne *AV* §I |

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
| `pushforwardOneForm` 🅒 | `Axioms/AbelJacobiMap.lean:143` | trace of 1-forms |
| `intersectionForm` | `Axioms/IntersectionForm.lean:59` | the pairing itself (properties are Class 1) |
| `LineBundle`, `H1`(+`instAddCommGroup`,`instModule`), `canonicalDivisor`, `LineBundle.ofDivisor` (6) | `RiemannSurface/LineBundle.lean:46–99` | line-bundle / sheaf-cohomology **type stubs**. `H0` is now `riemannRochSpace D` with inherited submodule instances; the `Divisor` triple and `PrincipalDivisors` were already discharged. |

### 2b. Definition-asserting axioms — *may mask a bad definition*

"My construction behaves correctly." These are the disguised risk: each
could be papering over a degenerate definition. Validation = discharge on a
concrete witness (see [`docs/validation-plan.md`](docs/validation-plan.md) §C).

| Axiom | File:Line | Note |
|-------|-----------|------|
| `AX_ofCurve_contMDiff` | `Axioms/AbelJacobiMap.lean:348` | Abel–Jacobi smoothness |
| `AX_pushforward_pullback` | `Axioms/AbelJacobiMap.lean:782` | push∘pull = deg multiplication |
| `AX_pushforwardAmbient_preserves_lattice` | `Axioms/AbelJacobiMap.lean:413` | period-map naturality |
| `AX_pullbackAmbient_preserves_lattice` | `Axioms/AbelJacobiMap.lean:427` | period-map naturality |
| `AX_pushforwardOneForm_id` / `_comp` | `Axioms/AbelJacobiMap.lean:241,248` | functoriality of trace |

*Retired 2026-06-05.* `AX_ofCurve_inj` is now a theorem in
`Axioms/OfCurveInjective.lean`, derived from the proved period-triangle theorem
`AX_Period_Triangle`, `AX_AbelTheorem`, and `principal_imp_eq_of_genus_pos`.

### 2c. Atlas / structure axioms — *curve-specific constructions*

Real chart/manifold constructions for specific curves; classically true,
discharge is substantial chart work. As of the Phase-3 batch (2026-06-04) the
unified `Hyperelliptic` and `PlaneCurve` *types* are now real `def`s; what
remains here is their **atlas/manifold** instances + the genus formula.

| Cluster | File:Lines | Count |
|---------|-----------|------:|
| `AX_Hyperelliptic_genus` only (type + `instTopologicalSpace`/`instChartedSpace`/`instIsManifold` + `oddEquiv`/`evenEquiv` discharged Phase-3; genus needs biholo, not just homeo) | `ProjectiveCurve/Hyperelliptic.lean` | 1 |
| `PlaneCurve`: `instNonempty` + 4 manifold/topology instances (`instCompactSpace`/`instConnectedSpace`/`instChartedSpace`/`instIsManifold`) + 2 affine props (`AX_PlaneCurveAffine_connected`, `AX_PlaneCurveAffine_noncompact`; type + `instTopologicalSpace` discharged Phase-3 Tier-1; `instT2Space` and affine `nonempty` now proved; projective `instNonempty` reverted in review) | `ProjectiveCurve/PlaneCurve.lean` | 7 |
| Odd-atlas infinity chart (`infinityChart`, `infinityInverseMap`, 4 compat, `mem_source`; the Phase-3 `infinityInverseMap` discharge was reverted in review) | `…/OddAtlas/InfinityChart.lean` | 7 |
| Even-atlas compatibility (`affineLiftChart_compat_…`, `…_compat_…`) | `…/Hyperelliptic/EvenAtlas.lean:243,252` | 2 |
| `AX_HyperellipticAffine_connected` | `…/Hyperelliptic/Basic.lean:101` | 1 |
| Elliptic witness (`AX_Elliptic_H1_symplectic`) | `…/Elliptic/Witnesses.lean:497` | 1; `AX_Elliptic_aLoop_analytic` (PR #86, 2026-06-06) and `AX_Elliptic_bLoop_analytic` (2026-06-07) were **discharged to theorems** via `extChartAt_quotient_mk_line_analyticAt`. |
| `AX_H1_ProjectiveLine_trivial` | `…/Line/Witnesses.lean:43` | 1 |

### 2d. Flagged — *true-but-unproven; needs end-to-end check*

The two cross-summand cocycle axioms that used to live here were **unsound**
(false for `deg g ≥ N/2−1`) and are now **retired** — see Recently
discharged. The other two — the Liouville hierarchy **L2/L3** (the classical
canonical-differentials theorem for hyperelliptic curves) — are now **proven
theorems** (2026-06-07, PR #96), so this class is now **empty**.

| Axiom | File:Line | Status |
|-------|-----------|--------|
| `AX_HyperellipticForm_polynomial_decomposition` (Liouville L2) | `Axioms/HyperellipticLiouville.lean` | **DISCHARGED → theorem** (2026-06-07, PR #96) — direct two-sheet σ-anti-invariance + `affCoeff` chart-transfer ⇒ single-sheet numerator entire + poly-growth ⇒ polynomial. |
| `AX_HyperellipticOneForm_eq_form` (Liouville L3) | `Axioms/HyperellipticLiouville.lean` | **DISCHARGED → theorem** (2026-06-07, PR #96) — L2 + cocycle propagation across branch/∞ charts + `ext_of_coeff`. |

---

## Universal-property axioms (discharge plan)

Deferred textbook leaves of [`docs/universal-property-proof-plan.md`] (proving
`Jacobians.IsJacobian x₀ (Jacobian X) (ofCurve x₀)` — the categoricity theorem).
All cross-model vetted **Gemini (gemini-3-pro-preview) + Codex, 2026-06-02**
(`GR`+`CX`); ratings **Standard**/**Likely correct**. UP-0 and the E-row
existence half (UP-1) are now used by
`Jacobians.jacobianUniversal_phi_exists`; factorization and uniqueness remain
future work.

| Axiom | Status | Reference |
|-------|--------|-----------|
| `AX_curve_generates_jacobian` | **stated** — `Axioms/TorusAlbanese.lean:168` | Mumford; Milne *AV* §I |
| `AX_torus_oneforms_dualCover` | **stated** — `Axioms/TorusAlbanese.lean:73` | Birkenhake–Lange Ch. 1 |
| `AX_torus_self_albanese` | **stated** — `Axioms/TorusAlbanese.lean:88` | Birkenhake–Lange Ch. 1 |
| `AX_period_functoriality` | **stated** — `Axioms/TorusAlbanese.lean:120` | Griffiths–Harris Ch. 0 & 2 |
| `AX_torus_descent_holo` | ✅ **DISCHARGED 2026-06-06** — now a `theorem` (see Recently discharged) | Birkenhake–Lange Ch. 1; quotient-manifold descent |

The direct holomorphicity step (E6 in the plan) was originally blocked by a
charted-space mismatch between `JacobianAmbient`'s `ComplexTorus` charts and
Kirov's raw quotient charts. That mismatch is now **resolved**: de-privatizing two
`ComplexTorus` chart lemmas (`extChartAt_symm_eq_quotient_mk`,
`mem_extChartAt_target_iff`) lets the descent be proved directly via Kirov's
quotient local-homeomorphism API, so `AX_torus_descent_holo` is a real theorem —
no fallback in use. The "every abstract torus hom is holomorphic" form remains
*false* (Codex-flagged) and was never the form used.
Step 0 (the `ConnectedSpace (Jacobian X)` instance needed
for the goal to typecheck) is **done** (`Jacobian/Construction.lean`,
`Challenge.lean`).

## Recently discharged (now axiom-free)

| Was axiom | Discharged via | Proof lives in |
|-----------|----------------|----------------|
| `contDiffOn_symm_toOpenPartialHomeomorph` *(2026-06-07)* | proved full-target statement under a new `h_global : ContDiff ℂ ω f` hypothesis, making the original false statement (which assumed only `ContDiffAt ℂ ω f a`) mathematically sound and provable | [InverseFunctionTheorem.lean](file:///d:/MATHS/jacobian-claude/jacobian-challenge-fork/Jacobians/GeneralResults/InverseFunctionTheorem.lean) |
| `AX_PlaneCurveAffine_nonempty` *(2026-06-07)* | dehomogenize to `affinePolynomial H.F.val`; `affinePolynomial_not_isUnit` plus `exists_eval_eq_zero_of_not_isUnit_mvPolynomial` gives a complex zero in the affine patch | `ProjectiveCurve/PlaneCurve.lean` |
| `AX_Period_Triangle` *(2026-06-06)* | conjugate the triangle loop to `Classical.arbitrary X`; use `loopDevValH1Hom_eq_loopIntegralToH1_apply` + `loop_canonicalArcIntegral_mem_periodLatticeInBasis` from the analytic cycle basis; cancel bridge/reverse periods by `canonicalArcIntegral_trans`/`_reverse` | `Axioms/AbelJacobiMap.lean`, `RiemannSurface/LoopIntegralHom.lean`, `RiemannSurface/ArcAlgebra.lean` |
| `AX_cycleBasisLoop_integrable` *(2026-06-06)* | `analyticArc_canonicalIntegrand_intervalIntegrable` from strong per-cell analytic witnesses; cycle-basis loops are ordinary `AnalyticArc`s | `RiemannSurface/LoopIntegral.lean`, `RiemannSurface/PartitionIndependence.lean` |
| `squareLocalHomeomorph_zero_notMem_source`, `polynomialLocalHomeomorph_no_critical_in_source` *(2026-06-06, PR #78)* | affine-form IFT-shape proved directly — square: distinct preimages collide under squaring ⇒ contradiction; polynomial: `ApproximatesLinearOn` / `HasFDerivAt` inverse-function argument | `ProjectiveCurve/Hyperelliptic/AffineForm.lean:66,280` |
| `AX_torus_descent_holo` *(2026-06-06)* | local-section route over Kirov's `ZLatticeQuotient` local-homeo API (`isLocalHomeomorph_mk` + `contDiffOn_symm_mk`) composed with `P.fromQuot_holo`; helper `complexTorus_pushforward_contMDiff_to_quotient` | `Axioms/TorusAlbanese.lean` |
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
| **Hyperelliptic type cascade** (6): `Hyperelliptic`, `instTopologicalSpace`, `instChartedSpace`, `instIsManifold`, `AX_Hyperelliptic_oddEquiv`, `AX_Hyperelliptic_evenEquiv` *(Phase 3, 2026-06-04)* | `Hyperelliptic` → `noncomputable def` as a pure parity dispatch `if h : Odd … then HyperellipticOdd H h else HyperellipticEvenProj H`; the instances are defined via `Decidable.casesOn` with an explicit motive (`carrierOf`/`topologicalSpaceOf`) so they reduce in lockstep with the carrier's `dite` (solving the dependent-`dite` defeq that defeats a naive `split`); the equivs are `Homeomorph`s and the 4 prop instances transport through them. **Kernel-verified:** `#print axioms Hyperelliptic` = the 3 standard (carrier is atlas-free), `instTopologicalSpace` standard-3, and `instChartedSpace`/`instIsManifold` correctly transport the (sound, unproven) odd-`infinityChart` + even-atlas-compat axioms — that is where the atlas dependency belongs. 6 named axioms → `def`/instances, **no NEW axioms**. | `ProjectiveCurve/Hyperelliptic.lean` |
| **PlaneCurve Tier-1** (3): `PlaneCurve`, `instTopologicalSpace`, `instT2Space` *(Phase 3 plus later T2 discharge)* | `PlaneCurve` → faithful subtype `def` of `Projectivization ℂ (Fin 3 → ℂ)` via a rep-independent existential predicate (`∃ v hv, mk v hv = p ∧ eval v = 0`, using `H.F.homogeneous`); topology from the subtype; `instT2Space` inherited from the proved `projectivization_t2Space`. `#print axioms PlaneCurve` = standard 3. `instNonempty` (it had rested on the *false* `AX_PlaneCurveAffine_nonempty`), `instCompactSpace`/`instConnectedSpace`, the atlas, and the affine props remain honest axioms. *(`infinityInverseMap`'s Phase-3 discharge was reverted in review — arbitrary-root `def`.)* | `ProjectiveCurve/PlaneCurve.lean` |

The two cocycle axioms (task #21, 2026-06-01) were the only **unsound**
axioms in the repo; their retirement makes `genus_HyperellipticEven_eq`
sound. The Liouville L2/L3 axioms are now **discharged** (PR #96). `hyperellipticForm`
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
#   prints 49 — the vendored Kirov subtree is now axiom-free, so 49 is the total.
# (lean needs a file argument, so write the snippet then run it:)
cat > /tmp/axcount.lean <<'LEAN'
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
lake env lean /tmp/axcount.lean   # → project axioms (non-vendor): 49

# text cross-check (9 doc-example lines are tagged `-- not-an-axiom`):
grep -rnE '^axiom ' Jacobians --include='*.lean' | grep -v '/Vendor/' | grep -v 'not-an-axiom' | wc -l
```
