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
