# B1 — puncture-lasso generation of π₁(ℂ ∖ T): the route

Date: 2026-06-12. Issue #171 (claimed in-thread), `SVK_BLOCKER.md` B1.
Branch `feat/svk-generation`. Companion to `SVK_ROUTE.md` (route (c) lower
half, delivered) and `docs/planning/SVK_BLOCKER.md` (B1/B2/B3 gap analysis).

## Target

**(B1)** For finite `T : Finset ℂ` and basepoint `x₀ : ((↑T : Set ℂ)ᶜ : Set ℂ)`:
the classes of the `exists_winding_dual_loops` lassos generate
`FundamentalGroup ((↑T : Set ℂ)ᶜ) x₀`. Membership form (matching the
`FiniteGoodCover` house pattern):

```
theorem fromPath_mem_lassoSubgroup
    (T : Finset ℂ) (x₀ : ...) (γ : Path x₀ x₀) :
    FundamentalGroup.fromPath ⟦γ⟧ ∈
      Subgroup.closure (Set.range (lassoClass T x₀))
```

This is the upper-bound half of issue #171's T1, sufficient on its own if
the B3 consumer answer weakens the contract to generation + H₁-independence
(asked in-thread 2026-06-12; B2 freeness deferred pending that answer).

## Why this is NOT a from-scratch SVK

Only the **generation half** of van Kampen is needed — no amalgamation, no
free-product normal forms, no pushout. The repo already contains the entire
analytic engine for generation-half statements, twice:

* `Jacobians/Topology/FiniteGoodCover.lean` —
  `exists_lebesgue_subdivision_iUnion` (Lebesgue subdivision of a loop over
  an arbitrary `iUnion` of opens), `homotopic_of_forall_mem_isSimplyConnected`,
  and crucially `fromPath_concat_conj_mem`: a **membership telescope** — the
  spoke-conjugated concatenation factors of a subdivided loop lie in any
  subgroup containing each conjugated arc class. The good-cover theorem
  `fundamentalGroup_fg_of_goodCover` is exactly the B1 proof *shape*, with
  "simply connected cells" where B1 has "cells with known π₁".
* the ported `KirovDolbeault/VanKampen.lean` telescoping core (same method,
  simple-connectivity conclusion).

What `fundamentalGroup_fg_of_goodCover` uses simple-connectedness for is
ONLY the factor classification (each conjugated arc class depends just on
indices). B1 replaces that step with the **M1 computation**: in a cell that
is a once-punctured disk/half-plane, every spoke-conjugated loop class is a
power of the cell's lasso (`pi1PuncturedPlaneIntAt` surjectivity transported
by a homeomorphism). Everything else is verbatim the same telescope.

## Rungs

| rung | statement | difficulty |
|---|---|---|
| **G1** two-open generation lemma | `X = U ∪ V` open, `U ∩ V` path-connected ∋ `x₀`: any subgroup `H` of `π₁(X, x₀)` containing every spoke-conjugated class of a loop lying in `U` and every one lying in `V` is `⊤`. Extract from the `FiniteGoodCover` telescope (specialize `exists_lebesgue_subdivision_iUnion` to two opens; junction points in `U ∩ V`, spokes inside `U ∩ V` by its path-connectedness; `fromPath_concat_conj_mem` finishes). Generalize to `n` opens with all pairwise intersections path-connected through a common `x₀`-region if it is no harder — but two-open + induction suffices. | **M** (extraction, not invention) |
| **G2** cell π₁ computation | a spoke-conjugated loop inside an open set homeomorphic to a once-punctured plane is, in `π₁` of that cell, a power of the cell's lasso: `pi1PuncturedPlaneIntAt` (M1) + `pi1MulEquivOfHomeomorph` (already in `PuncturedSpherePi1.lean`) + the generator pin `pi1PuncturedPlaneIntAt_ofAdd_one`. Also the degenerate cell (no puncture): convex/simply-connected ⟹ trivial class (`mk_eq_refl_of_mem_isSimplyConnected`, exists). | **E/M** (assembly of existing pieces) |
| **G3** separating-cover induction | order `T` by real part (perturb by a rotation so real parts are distinct — finitely many bad angles); split at a vertical line: `U` = open half-plane-minus-left-punctures, `V` = complementary half-plane-minus-right-punctures, `U ∩ V` = punctureless open strip (convex ⟹ path-connected ∋ x₀ after a basepoint transport). G1 reduces `π₁(ℂ∖T)` membership to `U`- and `V`-loop classes; each side is homeomorphic (affine map) to `ℂ ∖ T'` with `|T'| < |T|`; induct. Base `|T'| = 1` is G2; `|T'| = 0` is the degenerate cell. | **M/H** (the bookkeeping mass: homeos, basepoint transports) |
| **G4** lasso identification across the induction | the inductive generators (lassos of the half-plane copies, pushed into `ℂ∖T`) must land in `Subgroup.closure (range (lassoClass T))`. **This is the load-bearing subtlety**: two lassos around the same puncture with the same winding vector need NOT be equal in the non-abelian `π₁` — only conjugate-ish. Resolution: state G1/G3's conclusion relative to a SUBGROUP `H` that is (i) closed under conjugation by all classes (use the **normal closure** `Subgroup.normalClosure (range lassoClass)` during the induction) and (ii) prove at the end `normalClosure = closure` is unnecessary — generation by conjugates of lassos is what the consumer needs, OR keep plain closure and prove the spoke-difference conjugators are themselves products of lassos (they are loops in `ℂ∖T`, so this is circular UNLESS handled by strengthening the induction: prove generation for ALL basepoints/spokes simultaneously). **Decision pinned here: run the induction with `normalClosure`, then note `closure = normalClosure` follows once B2 freeness lands; ask the consumer (B3 answer) whether normal-closure generation suffices for the slit-sheet lift — it likely does, since monodromy images of conjugates are conjugates.** | **H** (the genuinely new content) |
| **G5** headline assembly | `fromPath_mem_lassoSubgroup` (normal-closure form), sphere transport via `pi1PuncturedSphere` | **E** |

## Deliverable plan (incremental PRs, per the issue's preference)

1. PR-1: `Jacobians/Topology/TwoOpenGeneration.lean` — G1 alone (reusable,
   self-contained, mergeable; valuable to Mathlib upstream).
2. PR-2: G2 + the affine/half-plane homeo toolkit.
3. PR-3: G3+G4+G5 — the induction and headline, with the G4 decision
   (normal closure) flagged in the PR body and on issue #171.

Standard-3 gate per file; no new axioms; statements `Path`-level and
basepointed per the issue's interface freeze.

## G3/G4 statement-design notes (2026-06-12, second pass)

**Trap recorded — the naive induction statement is FALSE.** "For H normal
containing, per puncture s, the class of SOME loop with winding vector δ_s:
H = ⊤" fails in general: winding pins only the abelianized image, and
quotients of free groups by one relator-per-generator with trivialized
abelianization can be nontrivial **perfect** groups (balanced presentations
of perfect groups). So the inductive hypothesis cannot be winding-level; it
must carry honest **cell-lasso** elements (G2's `cellLasso`, pinned up to
the cell's ℤ-iso, not up to winding).

**Consequences for the induction package.** P(n) must bundle:
(i) *meridian conjugacy*: any two cell-lassos around the same puncture
    (cells containing the basepoint) are conjugate in `π₁(ℂ ∖ T)` — for
    n = 1 this is free (π₁ ≅ ℤ, equal not just conjugate); inductively it
    rides along with (ii);
(ii) *normal generation*: the normal closure of one cell-lasso per puncture
    is ⊤.
The conceptual proof of (ii) — "filling the punctures kills exactly the
meridians" — is the AMALGAMATION half of SVK (kernel computation), which
the generation-only extraction deliberately avoided.  Two honest options:
  (a) prove the *filling* statement
      `π₁(ℂ∖T)/ncl(lasso_s) ≅ π₁(ℂ∖(T∖{s}))` directly by a covering-space
      argument (universal-cover surgery; heavy), or
  (b) run the separating-line induction with BOTH clauses in the package,
      using G1 for the generation step and the strip's convexity to keep
      conjugators tracked.  Sketch for (ii) at the induction step: G1 over
      {U, V} reduces any class to a product of U- and V-loop classes; the
      IH (transported through `halfPlaneHomeo` + `complCongr`) expresses
      each side-class in side-cell lassos; clause (i) (transported) plus
      strip-based conjugator paths rewrite side-cell lassos as conjugates
      of the chosen global cell-lassos.  The (i)-step at size n reduces to
      the (i)-step at size 1 inside a common refined cell — the n=1 case
      is the anchor.
Option (b) stays within the delivered machinery (G1 + G2 + toolkit) and is
the recommended route; its hard new content is the transport bookkeeping,
not new topology.  Estimated 1–2 focused sessions for (i)+(ii) at this
level of preparation.

Status: G1 ✓ (CoverGeneration), G2 ✓ (CellLassoPower), toolkit ✓
(halfPlaneHomeo + complCongr).  Next session: implement (b).

## G3 cell-shape resolution (2026-06-12, third pass)

Cell-shape analysis for the induction, recorded so the implementing session
starts decided:

* **Strip cells fail G1's hypotheses**: pairwise intersections of disjoint
  strips are empty and cannot all contain the basepoint.
* **T-shaped widenings (strip ∪ low corridor) are star-shaped, not convex**;
  star-shaped-open ≃ₜ ℂ is classically true but NOT in Mathlib at pin — a
  dead end for G2's homeo presentation.
* **Decision: binary-split recursion over `fromPath_mem_of_two_open`** (the
  delivered two-open corollary), never the n-open form: split at a
  puncture-free vertical strip, `U`/`V` = half-planes minus their punctures
  (path-connected, once the strip holds the basepoint — transport by
  conjugation, `PunctureLoops.fundamentalGroupMulEquivOfPath_fromPath`),
  `U ∩ V` = the convex strip.  Each side transports to a smaller
  configuration through `halfPlaneHomeo` + `complCongr` — both delivered.
  The package P(T) is proved by strong induction on `T.card` with the two
  clauses of the second-pass notes; meridian conjugacy (clause (i)) at the
  glue step uses a common disk-cell refinement near the puncture — the one
  remaining piece of new construction (a disk ≃ₜ plane homeo with center
  transport, same OrderIso pattern as `halfPlaneHomeo` radially, OR observe
  that the binary recursion only ever compares a side-cell lasso with the
  global cell lasso around the SAME puncture inside the SAME half-plane
  side, where the side IS a common once-punctured cell — check this first:
  if every comparison in the recursion is intra-side, clause (i) reduces to
  the n = 1 anchor `closure_circleAround_eq_top` + G2 uniqueness inside one
  cell, and no disk toolkit is needed.)

## G3/G4 fourth pass (2026-06-12) — the endgame named

Working the glue lemma to its foundation:

1. **Cell definition v2.** `PuncturedCellSystem` cells should be *paired*
   presentations `φ : (W_s, s) ≃ₜ (ℂ, 0)` (cell = `W_s ∖ {s}`, `W_s` open in
   the s-filled space): the punctured cell is then automatically a
   once-punctured plane (restriction of `φ`) AND the filled cell is simply
   connected — both G2 and the filling argument apply.  Mechanical refactor
   of the delivered statement layer.
2. **The mountain, precisely.** Every glue route (side-system lassos into
   the global normal closure) reduces to ONE named lemma — the filling
   kernel: *a loop in `X = ℂ∖T` that is nullhomotopic in the s-filled space
   `Y = ℂ∖(T∖{s})` lies in `ncl(meridian of any paired cell around s)`.*
   This is presentation-level SVK content and cannot be avoided by
   generation-only tricks (the |T|=1 universe-cell trick does not scale:
   there is no common cell).  Provable by the classical square-grid
   argument: 2D Lebesgue subdivision of the nullhomotopy `I×I → Y`, cells
   meeting `s` replaced by punctured detours costing `ncl(meridian)`
   factors — i.e. a **2D homotopy-telescope** sibling of the delivered
   1D membership telescope.  Substantial but well-understood; this is the
   true multi-week core of B1 (and of any identified-generator π₁
   computation of the punctured plane).
3. **Split-line preprocessing** (distinct projections): pick `c` between
   the real parts of any two punctures avoiding the finite set `re '' T`;
   ties among other punctures are harmless.  All-equal-re configurations
   use the imaginary split (axis-swap reflection is orientation-reversing
   but the winding pin is ±-symmetric).
4. **Decision point (B3, escalated on issue #171).** If the slit-sheet
   consumer needs only H₁-level generation, the δ-winding matrix already
   delivered may suffice and the 2D telescope can be deferred to the
   Mathlib-grade T1 contract; if the full T1 is needed, the 2D telescope
   is the next campaign and should be planned as its own lane.
