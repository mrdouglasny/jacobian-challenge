# Albanese discharge — STATUS (present state + what's left)

*Updated 2026-06-15, after PR #253 merged (`dc69563`).* This was the plan to discharge
the three Albanese torus axioms (G2/G3/G4) behind the categoricity capstone
`ofCurve_isJacobian`; it is now mostly **done**. Below: what landed, the machine-verified
axiom closures, and the (optional, scoped) remaining work.

## Where it stands

The Albanese categoricity result is now **off the torus axioms**. Machine-verified
(`#print axioms`) on `main`:

| Theorem | closure |
|---|---|
| `isJacobian_unique` (abstract categoricity: any two objects with the universal property are uniquely isomorphic) | `[propext, Classical.choice, Quot.sound]` — **axiom-free** |
| `ofCurve_isJacobian` (our construction satisfies the universal property) | std-3 + `AX_curve_image_subgroup_isOpen` (**AK**) only |
| `isJacobian_iso_jacobian` (the universal property pins Buzzard's `Jacobian X`) | std-3 + **AK** only |
| `torus_self_albanese` (G2), `period_functoriality` (G3) | std-3 — **axiom-free** |
| `curve_generates_jacobian` (G4) | std-3 + **AK** |

`AX_torus_uniformization` (A1) is **declared but OUT of every headline closure** (no global
instance). The 24 Buzzard-challenge headlines remain axiom-free and are unaffected.

## What it takes to completely pin the Jacobian

"Pinning the Jacobian" = **uniqueness** + **existence**:

| ingredient | theorem | status |
|---|---|---|
| **Uniqueness** — any two objects with the universal property are *uniquely* isomorphic (so "the Jacobian" is well-defined up to unique iso) | `isJacobian_unique` | ✅ **done, axiom-free** (std-3) |
| **Existence** — our concrete `ℂ^g/Λ` actually *is* such an object (a realizer exists) | `ofCurve_isJacobian` | proved, rests on **AK** |
| **The Jacobian is *that* object** — Buzzard's `Jacobian X` ≅ any Jacobian-object, uniquely | `isJacobian_iso_jacobian` | proved, rests on **AK** (+ a presentation hypothesis on `Jacobian X`) |

So the definition is **already pinned up to unique isomorphism, axiom-free** (the `isJacobian_unique`
half). To make the *pinning of Buzzard's concrete Jacobian* **completely axiom-free**, all that
remains is:

1. **Discharge AK** (`AX_curve_image_subgroup_isOpen`) — the ~25-decl Kirov port (item (a) below).
   This is the *only* remaining mathematical content; it makes `ofCurve_isJacobian` /
   `isJacobian_iso_jacobian` rest on the standard 3 Lean axioms.
2. **Supply the concrete `Jacobian X` presentation instance** (item (c) below, axiom-free) — drops the
   hypothesis on `isJacobian_iso_jacobian`, making it **unconditional**.

That is the whole list. **`AX_torus_exp` / abstract-`A` generality (item (b)) is NOT needed to pin
the Jacobian** — the presented-torus universal property already pins it; (b) only *additionally*
extends categoricity to abstract (non-presented) tori, an optional strengthening.

## What landed (PR #253)

- **Soundness fix.** `TorusSelfAlbanesePresentation.liftCoord_eq_albanese` was an *unsatisfiable*
  field (the `=` form forced all loop periods equal — `0 = −1` on `ℂ/Λ`), so the old
  `AX_torus_self_albanese` was a **false axiom**. Reworked to the sound mod-Λ congruence;
  Gemini 3.1-pro re-vetted satisfiable. (Off the Buzzard-24 path.)
- **G3 bridge proved.** `period_functoriality` discharged from the interface via a genuine
  developing-map H₁-naturality argument: `analyticLoopsGenerateH1` (loops surject onto H₁) +
  a chart chain-rule naturality + the self-Albanese torus loop-period lemma. No new axiom.
- **Repoint.** Wired the proven G2/G3/G4 theorems into the headline; **retired the 3 legacy
  torus axioms** (`AX_torus_self_albanese` / `AX_period_functoriality` /
  `AX_curve_generates_jacobian`).
- **Escape hatch.** `TorusSelfAlbanesePresentation` is now a **class**: the universal property
  ranges over *presented* complex tori (target `A` carries `[TorusSelfAlbanesePresentation m A]`),
  so A1 leaves the headline closure entirely. This is the standard convention — a complex
  torus *is* `ℂ^m/Λ`; uniformizing an abstract Lie group is separate Lie theory.

## Remaining work (all optional, individually scoped)

### (a) AK → 0 — make the Albanese *fully* axiom-free
`AX_curve_image_subgroup_isOpen` (AK, local Jacobi inversion) is the one remaining axiom under
`ofCurve_isJacobian` / `isJacobian_iso_jacobian`. **Decl-level scoped** (not the misleading
module-import cone): the true footprint is **~25 declarations across 5 files** (`JacobiLocalMap`,
`JacobiBasePoints`, + 3/5/1 cherry-picked decls from `OfCurveAnalyticitySkeleton` / `SmoothPathCore`
/ `ResidueCalculus.FormCoeff`) — the `MappingDegree`/`LocalMultiplicity`/`Surface` branches are
NOT needed (`exists_jacobiBasePoints_det_ne_zero` is a linear-algebra rank argument, not
branched-cover theory). Small enough to **reimplement-with-citation** rather than verbatim-vendor.
Full analysis: [`ALBANESE_REPOINT_REFACTOR.md`](ALBANESE_REPOINT_REFACTOR.md).

### (b) Abstract-`A` generality — quarantined exp axiom
The escape hatch makes the headline range over *presented* tori. To recover categoricity against
an **abstract** compact connected complex Lie group, add a quarantined
`AbstractTorusUniformization.lean` providing a `TorusSelfAlbanesePresentation` for abstract `A`
from a **minimal** axiom `AX_torus_exp` (`exp : ℂ^m →+ A`, holomorphic, `mfderiv exp 0 = id`) +
the lattice/quotient/self-Albanese **deduction** (all theorems: `ker exp` a full `ZLattice` via IFT
+ the open-subgroup-of-connected argument reused from G4; `A ≅ ℂ^m/Λ` via the quotient manifold;
the self-Albanese identity via `exp`-pullback = constant covector + FTC). `AX_torus_exp` is
deep-think-vetted (the `mfderiv = id` normalization is *necessary*; satisfiable witness `ℂ^m/Λ`).
A full axiom-free `exp` build is months-scale (Mathlib lacks Lie-exp / manifold flows / universal
cover). Spec + vetting: [`A1_THINNING_PLAN.md`](A1_THINNING_PLAN.md),
[`A1_DEEPTHINK_BRIEF.md`](A1_DEEPTHINK_BRIEF.md).

### (c) Concrete `Jacobian X` presentation instance
`isJacobian_iso_jacobian` currently takes `[TorusSelfAlbanesePresentation (genus X) (Jacobian X)]`
as a **hypothesis**. To make it *unconditional*, build that instance concretely from the period
lattice (axiom-free — the `ℂ^g/Λ` self-Albanese identity, derivable from the existing period/loop
machinery). This is also the concrete special case of the (b) deduction.

---

*Historical note:* the original "minimal new axiom set" analysis (reduce 3 → A1 + a Kirov-vendored
G4) is superseded by the above; A1 itself is now out of the closure via the typeclass reframe.
Related: [`ALBANESE_REPOINT_REFACTOR.md`](ALBANESE_REPOINT_REFACTOR.md) (repoint + Kirov-AK
decl-level scoping), [`A1_THINNING_PLAN.md`](A1_THINNING_PLAN.md) (exp-axiom thinning + escape
hatch + deep-think verdict), [`A1_DEEPTHINK_BRIEF.md`](A1_DEEPTHINK_BRIEF.md) (external-review
brief). Axiom ledger: [`../../AXIOM_AUDIT.md`](../../AXIOM_AUDIT.md).
