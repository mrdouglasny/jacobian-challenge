# Axiom audit — jacobian-challenge

*Last updated 2026-05-31.*

In this project an **axiom** is a staging point: a statement we use before
its Lean proof is assembled, with the trust boundary kept explicit and the
discharge tracked. The goal is for every entry below to become a proved
theorem. Format conventions: [`~/.claude/AXIOM_AUDIT_FORMAT.md`]; deep
per-declaration trace: [`docs/dependency-trace.md`](docs/dependency-trace.md);
machine-checked dependency of every headline:
[`docs/axiom-report.txt`](docs/axiom-report.txt).

**Active project axioms: 95** — **93** in our modules + **2** vendored Kirov
`:= sorry` declarations restated as named axioms. (Verified against the
kernel, not a text scan — see [Verification](#verification). A text scan of
`^axiom ` also reports 93 once the 9 doc-comment example lines tagged
`-- not-an-axiom` are excluded.)

---

## Triage

Per the review plan, axioms are split into two classes:

- **Class 1 — standard form, textbook-proven** (14 axioms). Statements are
  the standard textbook ones, citable, with no ambiguity about their form;
  discharging them is "port the textbook proof / wait for Mathlib." These
  are the *trusted* axioms.
- **Class 2 — form or proof not yet clear** (81 axioms). Either the Lean
  encoding is a project-specific stub whose faithfulness needs checking, or
  the statement asserts good behaviour of one of our constructions (and
  could mask a bad definition), or it is a large atlas/analysis fact with no
  obvious discharge. **This is the class to focus on.** Subdivided 2a–2d
  below, with 2d (Flagged) the most urgent.

| Class | Count | Nature | Trust |
|------|------:|--------|-------|
| 1 — textbook-standard | 14 | classical theorems, citable | high |
| 2a — data-existence | 27 | "this function/object exists with spec S" | spec needs review |
| 2b — definition-asserting | 11 | "my construction has good property P" | **may mask a bad def** |
| 2c — atlas / structure | 39 | curve-specific chart constructions | real but unverified |
| 2d — **flagged** | 4 | known concern / unsound at edge | **do not trust downstream as-is** |

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
| `AX_BranchLocus` | `Axioms/BranchLocus.lean:70` | degree / branch-locus finiteness, Miranda Ch. II |
| `AX_PluckerFormula` | `Axioms/PluckerFormula.lean:55` | Griffiths–Harris Ch. 2 (Plücker) |
| `AX_genus_eq_zero_iff_homeo` | `Axioms/Uniformization0.lean:55` | uniformization, genus 0 (Forster §27) |
| `AX_AnalyticCycleBasis` | `Axioms/AnalyticCycleBasis.lean:257` | symplectic H₁ basis (standard) |
| `AX_IntersectionForm_alternating` | `Axioms/IntersectionForm.lean:66` | cup product on H₁ (standard) |
| `AX_IntersectionForm_perfect` | `Axioms/IntersectionForm.lean:91` | Poincaré duality / unimodularity |
| `AX_PeriodLattice` | `Axioms/PeriodLattice.lean:92` | period lattice is a full ℤ-lattice |
| `instPeriodLatticeDiscrete` | `Axioms/PeriodLattice.lean:77` | discreteness of the period lattice |
| `Vendor.Kirov…genus_eq_zero_iff_homeo` | `Vendor/Kirov/Genus.lean:94` | uniformization (Kirov handoff) |
| `Vendor.Kirov…ambientPhi_ambientPsi_eq` | `Vendor/Kirov/HolomorphicForms.lean:340` | degree identity (Kirov handoff) |

*Note.* `AX_genus_eq_zero_iff_homeo` is still an axiom **only** for the
abstract `genus_eq_zero_iff_homeo`; the concrete `genus ℙ¹ = 0` no longer
uses it (proven directly — see Recently discharged).

---

## Class 2 — form or proof not yet clear  *(the focus)*

### 2a. Data-existence axioms — *the spec is the question*

"This function/object exists satisfying spec S." Risk: the spec is vacuous
or contradictory, or doesn't pin down the intended object. The five marked
🅒 have written construction plans in
[`docs/construction-plans/`](docs/construction-plans/).

| Axiom | File:Line | Note |
|-------|-----------|------|
| `pathIntegralBasepointFunctional` 🅒 | `Axioms/AbelJacobiMap.lean:96` | the path-integral functional; **opaque** (see `ofCurve` card) |
| `AX_pathIntegral_local_antiderivative` | `Axioms/AbelJacobiMap.lean:114` | chart-local FTC binding the functional to the cocycle |
| `loopIntegralToH1` 🅒 | `RiemannSurface/PathIntegral.lean:101` | H₁-level period descent |
| `pullbackOneForm` 🅒 | `Axioms/AbelJacobiMap.lean:130` | pullback of 1-forms |
| `pushforwardOneForm` 🅒 | `Axioms/AbelJacobiMap.lean:143` | trace of 1-forms |
| `localOrder` 🅒 | `Axioms/BranchLocus.lean:62` | local multiplicity of a holomorphic map |
| `intersectionForm` | `Axioms/IntersectionForm.lean:59` | the pairing itself (properties are Class 1) |
| `abelJacobiDiv` | `Axioms/AbelTheorem.lean:60` | divisor-level Abel–Jacobi |
| `bridgePath` (+5: `_continuous`, `_chart_differentiable`, `_at_zero`, `_at_one`, `_lineIntegrable`) | `Bridge/KirovLineIntegral.lean:164,167,182,188,191,212` | path-selection for the Kirov line-integral bridge |
| `Divisor`, `Divisor.instAddCommGroup`, `Divisor.deg`, `PrincipalDivisors`, `LineBundle`, `H0`(+`instAddCommGroup`,`instModule`), `H1`(+`instAddCommGroup`,`instModule`), `canonicalDivisor`, `LineBundle.ofDivisor` (13) | `RiemannSurface/LineBundle.lean:51–128` | line-bundle / sheaf-cohomology **type stubs** — form most in question |

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
| `AX_pullbackOneForm_id` / `_comp` | `Axioms/AbelJacobiMap.lean:158,165` | functoriality of pullback |
| `AX_pushforwardOneForm_id` / `_comp` | `Axioms/AbelJacobiMap.lean:178,185` | functoriality of trace |

### 2c. Atlas / structure axioms — *curve-specific constructions*

Real chart/manifold constructions for specific curves; classically true,
discharge is substantial chart work. The unified `Hyperelliptic` and
`PlaneCurve` types are axiomatized along with their 7 typeclass instances.

| Cluster | File:Lines | Count |
|---------|-----------|------:|
| `Hyperelliptic` type + 7 instances + `oddEquiv`/`evenEquiv`/`genus` | `ProjectiveCurve/Hyperelliptic.lean:59–104` | 11 |
| `PlaneCurve` type + 7 instances + 3 affine props | `ProjectiveCurve/PlaneCurve.lean:103–185` | 11 |
| Odd-atlas infinity chart (`infinityChart`, `infinityInverseMap`, 4 compat, mem_source) | `…/OddAtlas/InfinityChart.lean:48–102` | 7 |
| Even-atlas compatibility (`affineLiftChart_compat_…`, `…_compat_…`) | `…/Hyperelliptic/EvenAtlas.lean:243,252` | 2 |
| Affine-form IFT-shape (`squareLocalHomeomorph_zero_notMem_source`, `polynomialLocalHomeomorph_no_critical_in_source`) | `…/Hyperelliptic/AffineForm.lean:66,222` | 2 |
| `AX_HyperellipticAffine_connected` | `…/Hyperelliptic/Basic.lean:101` | 1 |
| `contDiffOn_symm_toOpenPartialHomeomorph` (narrow IFT gap) | `GeneralResults/InverseFunctionTheorem.lean:9` | 1 |
| Elliptic witnesses (`AX_Elliptic_aLoop_analytic`, `_bLoop_analytic`, `_H1_symplectic`) | `…/Elliptic/Witnesses.lean:86,90,166` | 3 |
| `AX_H1_ProjectiveLine_trivial` | `…/Line/Witnesses.lean:43` | 1 |

### 2d. Flagged — *known concern, do not trust downstream as-is*

> ⚠️ **The two cocycle axioms are UNSOUND — false as stated, not merely
> unproven.** Each asserts a cocycle *equation* under the hypothesis
> `g_inf = infReverse H g_aff`, which is always satisfiable (`rfl` in
> `hyperellipticForm`) and does **not** restrict the degree. `infReverse`
> is the genuine Möbius gluing only for `deg g_aff ≤ N/2−2`; at higher
> degree the equation is false, so the axiom is a false proposition under
> satisfiable hypotheses → the environment is strictly inconsistent.
> Deriving `False` is obstructed only by the noncomputability of
> `Quotient.out`, so no contradiction has been exhibited — but the trust
> boundary is broken. **`genus_HyperellipticEven_eq` (and `…_le`)
> transitively depend on these, so the even-genus headline is not yet a
> sound proof.** The matching low-degree statements are already **proven
> theorems** in `EvenForm.lean` (`cross_summand_cocycle_coord`, ~line 1238,
> under `hDeg : g_aff.natDegree < N/2−1`); **task #21** is to add `hDeg` to
> the axioms and thread it through `hyperellipticForm` /
> `hyperellipticFormLinearMap` (→ `Polynomial.degreeLT ℂ (N/2−1)`),
> retiring them. Plumbing, not new mathematics.

| Axiom | File:Line | Status |
|-------|-----------|--------|
| `hyperellipticEvenCoeff_cocycle_inl_inr_axiom` | `…/Hyperelliptic/EvenForm.lean:380` | **unsound** (false for `deg g ≥ N/2−1`); real low-degree theorem exists; load-bearing for the even-genus theorem. Task #21. |
| `hyperellipticEvenCoeff_cocycle_inr_inl_axiom` | `…/Hyperelliptic/EvenForm.lean:397` | **unsound**, same; discharge via the swap lemma from `inl_inr` once degree-bounded. Task #21. |
| `AX_HyperellipticForm_polynomial_decomposition` (Liouville L2) | `Axioms/HyperellipticLiouville.lean:215` | true-but-unproven (not unsound). **Step 4 of its proof plan is now proven** (`differentiable_eq_polynomial_of_growth`); steps 1–3 (branch-point regularity + degree-at-∞) remain. |
| `AX_HyperellipticOneForm_eq_form` (Liouville L3) | `Axioms/HyperellipticLiouville.lean:260` | true-but-unproven. Surjectivity of `hyperellipticForm`; consumes L2 + the flagged cocycle axioms. Feeds `genus_HyperellipticEven_le`. |

**Priority.** The two cocycle axioms (unsound) outrank everything else in
the audit: they break the trust boundary of a headline theorem.

**Task #21 progress (2026-05-31).** *Part 1 (the hard math) is DONE* —
both directions are now real, axiom-free theorems
(`hyperellipticEvenCoeff_cocycle_inl_inr` and the new `…_inr_inl`, the
latter via the general `transition_fderiv_mul` chart-transition symmetry in
`GeneralResults/ChartTransition.lean`). *Part 2 (plumbing)* — thread `hDeg`
from these theorems up through `hyperellipticForm` and delete the axioms —
is a ~150–250 LOC mechanical cascade scoped step-by-step in
[`docs/task-21-discharge-plan.md`](docs/task-21-discharge-plan.md). Until
Part 2 lands, the two axioms remain wired into `_satisfiesCotangentCocycle`
and the even-genus theorem is still not sound.

---

## Recently discharged (now axiom-free)

| Was axiom | Discharged via | Proof lives in |
|-----------|----------------|----------------|
| `AX_FiniteDimOneForms` | injective bridge to Kirov's Montel theorem | `Bridge/KirovHolomorphic.lean` |
| `genus ℙ¹ = 0` *(via `AX_genus_eq_zero_iff_homeo`)* | direct chart-cocycle + Liouville ⇒ `HolomorphicOneForm ℙ¹` subsingleton | `ProjectiveCurve/Line/OneForm.lean` |
| `AX_Liouville_compact_complex_manifold` (Liouville L1) | global max-modulus (`Complex.eqOn_…isMaxOn_norm`) + clopen connectedness | `Axioms/HyperellipticLiouville.lean` (`liouville_compact_complex_manifold`) |
| Liouville L2 **step 4** (growth ⇒ polynomial) | induction + Liouville + `dslope` | `GeneralResults/EntireGrowth.lean` (`differentiable_eq_polynomial_of_growth`) |

All four verified core-axioms-only via `#print axioms`.

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
#   prints 93; add the 2 Vendor/Kirov axioms for the total 95.
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
