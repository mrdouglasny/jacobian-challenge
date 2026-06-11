# SVK blocker — what separates "δ-winding lasso family" from "π₁ free"

Date: 2026-06-10. Branch `feat/topology-svk-lite`. Companion to
`SVK_ROUTE.md` (route decision) and `SVK_PROGRESS.log`.

## What is DONE (this branch, all sorry-free, standard-3 `#print axioms`)

| Milestone | Result | Where |
|---|---|---|
| M1 | `π₁(ℂ ∖ {a}, ·) ≃* Multiplicative ℤ`, generator = explicit circle loop, any basepoint, any radius | `Jacobians/Topology/CoveringPi1.lean`, `PuncturedPlanePi1.lean` |
| M2-lite | `windingHom : π₁(ℂ ∖ S, x₀) →* Multiplicative ℤ` per puncture + computation rules (lift displacement; convex avoidance) | `WindingNumber.lean` |
| M3-partial | `exists_winding_dual_loops`: for finite `T`, explicit lasso loops `L_s` with winding matrix `w_{s'}(L_s) = δ_{s,s'}` | `PunctureLoops.lean` |

M3-partial is the **lower-bound half** of "π₁(ℂ∖T) is free on loops around the
punctures": the lassos are ℤ-independent (any relation dies under the winding
vector), with the generators *identified* as concrete loops — the form the
slit-sheet consumer of `AX_PeriodCycleBasis` needs first. At the H₁ level it
says the classes of `L_s` span a free abelian ℤ^T-summand-image; combined with
a future generation statement it pins `H₁(ℂ∖T) ≅ ℤ^T` with the lassos as basis.

## What is NOT done, and why (the actual blockers)

**(B1) Generation (upper bound).** "Every loop class in `π₁(ℂ ∖ T, x₀)` is a
product of conjugates of the lassos." No Mathlib support. Two honest routes:

- *Two-open SVK induction* — needs the π₁-presentation form of Seifert–van
  Kampen (free product with amalgamation / groupoid pushout), absent from
  Mathlib in any form (`CategoryTheory/Limits/VanKampen.lean` is the
  categorical colimit notion, unrelated in practice). Building even the
  two-open group-level SVK with the standard Lebesgue-subdivision proof is a
  known multi-week project; the word-level bookkeeping (subdividing a loop,
  inserting connecting paths, regrouping into letters) is the dominant cost.
  Kirov's vendored `VanKampen.lean` (simple-connectivity corollary only)
  de-risks the subdivision/telescoping method but contains none of the
  word/normal-form layer.
- *Grid/subdivision generation directly for ℂ∖T* — subdivide a loop into
  cells avoiding T, write it as a product of cell-boundary conjugates, and
  collapse cells not containing punctures. Avoids stating SVK but reproves
  its hard half in a special case; estimated comparable effort (2–5 weeks),
  with the advantage that the output is exactly the consumer statement.

**(B2) Freeness (no relations beyond the free ones).** Even with generation,
"free on the lassos" needs injectivity of `FreeGroup T →* π₁(ℂ∖T)`, which the
abelian winding vector cannot see (commutators). Standard proofs: SVK
induction (again), or the action on the universal-cover tree / Ping-Pong with
explicit half-plane domains. Ping-pong on `ℂ∖T` requires concrete
fundamental-domain geometry — feasible but another multi-week block, and
Nielsen–Schreier (in Mathlib) does not help without a free ambient group.

**(B3) What the consumer actually needs.** Per
`CYCLEBASIS_ALTERNATIVES.md` §2b, the slit-sheet program consumes π₁/H₁ of the
punctured *sphere* through monodromy bookkeeping of a branched cover. The
H₁-level statement (free abelian basis of puncture loops) suffices for
period-lattice rank bookkeeping; full nonabelian freeness is only needed if
the monodromy argument is run at the π₁ level. Recommendation: when the
keystone lands and direction 2b starts, first check whether the H₁ statement
(= B1 + abelianized counting, NO B2) covers the need — it halves the blocker.

## Recommended next steps (in order)

1. ~~M4 sphere transport~~ — DONE this session (`PuncturedSpherePi1.lean`:
   `pi1MulEquivOfHomeomorph`, `puncturedSphereHomeo`, `pi1PuncturedSphere`,
   `pi1SphereTwoPoints`).
2. (medium) H₁ packaging: `H₁(ℂ∖T)`-level independence statement in the
   `Homology.lean` shape (`Additive (Abelianization (FundamentalGroup ...))`),
   so the slit-sheet consumer can use the lassos without π₁ plumbing.
3. (multi-week, separate workstream) B1 via the grid-generation route, scoped
   as its own quest; B2 only if the 2b monodromy argument turns out to need
   nonabelian freeness.
