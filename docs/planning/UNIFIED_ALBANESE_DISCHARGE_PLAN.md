# Albanese discharge — STATUS (present state + what's left)

*Updated 2026-06-15, after PR #253 merged (`dc69563`).* This was the plan to discharge
the three Albanese torus axioms (G2/G3/G4) behind the categoricity capstone
`ofCurve_isJacobian`; it is now mostly **done**. Below: what landed, the machine-verified
axiom closures, and the (scoped) remaining work — split into two levels (categoricity among
*presented* tori, axiom-free now, vs. among *abstract* tori, which needs the uniformization input).

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

**The subtlety (read this — it determines what "remains").** `isJacobian_unique` carries a
*presentation hypothesis on the objects themselves*
(`[TorusSelfAlbanesePresentation g₁ J₁] [TorusSelfAlbanesePresentation g₂ J₂]`). This is **not**
intrinsic to uniqueness — it is the price of the escape hatch. The universal property was restricted
to range over *presented* targets; the categoricity proof feeds `J₂` as a target of `J₁`'s universal
property (and vice-versa), and the universal property only *accepts* presented targets — so both
`J₁` and `J₂` must carry a presentation. Hence there are **two genuinely different categoricity
statements**, and which one you want decides what remains:

### Level 1 — categoricity among *presented* tori (axiom-free now; the standard convention)
A "complex torus" *is* `ℂ^g/Λ` by definition (Griffiths–Harris, Birkenhake–Lange), so the
`[TorusSelfAlbanesePresentation]` binder is **not** extra structure — it is just "the object is a
complex torus in the textbook sense." At this level `isJacobian_unique` is **axiom-free**, and to make
the pinning of Buzzard's concrete `Jacobian X` **fully axiom-free and unconditional** all that remains is:
1. **Discharge AK** (`AX_curve_image_subgroup_isOpen`) — the ~25-decl Kirov port (item (a) below); the
   *only* remaining mathematical content. Makes `ofCurve_isJacobian` / `isJacobian_iso_jacobian` std-3.
2. **Supply the concrete `Jacobian X` presentation instance** (item (c) below, axiom-free) — drops the
   presentation hypothesis on `isJacobian_iso_jacobian`, making it unconditional.

### Level 2 — categoricity among *abstract* tori, no presentation assumed (strictly stronger)
The presentation-free statement — *any two abstract compact connected complex Lie group tori
satisfying the universal property are uniquely isomorphic* — genuinely **requires `A1` /
`AX_torus_exp`** (item (b)). To use an abstract competitor `J₂` as a *target* you must first
**derive** its `ℂ^g/Λ` presentation, and that derivation **is** the uniformization theorem. The whole
difference between Level 1 and Level 2 is whether the competing object's presentation is **assumed**
(Level 1) or **derived** (Level 2). So **(b) is *not* "optional generality"** — it is precisely what
removes the presentation hypothesis from the categoricity statement.

**Honest summary.** The conceptual result — the Jacobian is determined up to unique isomorphism — is
done and axiom-free *for complex tori in the standard `ℂ^g/Λ` sense* (Level 1). Two independent
upgrades remain: AK + (c) make the concrete Level-1 pinning fully axiom-free; (b) lifts the whole
result to abstract tori by dropping the presentation hypothesis. They are orthogonal.

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

## Remaining work (scoped)

Grouped by the two levels above: **(a)+(c) complete Level 1** (concrete pinning, fully axiom-free,
presented tori); **(b) is required for Level 2** (drops the presentation hypothesis — categoricity
against abstract tori). (a)/(c) are axiom-free; (b) introduces one minimal axiom (or a months-scale
`exp` build). All three are independent.

### (a) AK → 0 — make the Albanese *fully* axiom-free  *(Level 1)*
`AX_curve_image_subgroup_isOpen` (AK, local Jacobi inversion) is the one remaining axiom under
`ofCurve_isJacobian` / `isJacobian_iso_jacobian`. **Decl-level scoped** (not the misleading
module-import cone): the true footprint is **~25 declarations across 5 files** (`JacobiLocalMap`,
`JacobiBasePoints`, + 3/5/1 cherry-picked decls from `OfCurveAnalyticitySkeleton` / `SmoothPathCore`
/ `ResidueCalculus.FormCoeff`) — the `MappingDegree`/`LocalMultiplicity`/`Surface` branches are
NOT needed (`exists_jacobiBasePoints_det_ne_zero` is a linear-algebra rank argument, not
branched-cover theory). Small enough to **reimplement-with-citation** rather than verbatim-vendor.
Full analysis: [`ALBANESE_REPOINT_REFACTOR.md`](ALBANESE_REPOINT_REFACTOR.md).

### (b) Abstract-`A` generality — quarantined exp axiom  *(Level 2 — required, not optional, for the presentation-free statement)*
The escape hatch makes the headline range over *presented* tori, which leaves a presentation
hypothesis on the objects in `isJacobian_unique`/`isJacobian_iso_jacobian`. Removing that hypothesis
— categoricity against an **abstract** compact connected complex Lie group — add a quarantined
`AbstractTorusUniformization.lean` providing a `TorusSelfAlbanesePresentation` for abstract `A`
from a **minimal** axiom `AX_torus_exp` (`exp : ℂ^m →+ A`, holomorphic, `mfderiv exp 0 = id`) +
the lattice/quotient/self-Albanese **deduction** (all theorems: `ker exp` a full `ZLattice` via IFT
+ the open-subgroup-of-connected argument reused from G4; `A ≅ ℂ^m/Λ` via the quotient manifold;
the self-Albanese identity via `exp`-pullback = constant covector + FTC). `AX_torus_exp` is
deep-think-vetted (the `mfderiv = id` normalization is *necessary*; satisfiable witness `ℂ^m/Λ`).
A full axiom-free `exp` build is months-scale (Mathlib lacks Lie-exp / manifold flows / universal
cover). Spec + vetting: [`A1_THINNING_PLAN.md`](A1_THINNING_PLAN.md),
[`A1_DEEPTHINK_BRIEF.md`](A1_DEEPTHINK_BRIEF.md).

### (c) Concrete `Jacobian X` presentation instance  *(Level 1)*
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
