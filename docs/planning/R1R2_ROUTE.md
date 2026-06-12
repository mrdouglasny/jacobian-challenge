# R1/R2 route — the Hodge half of `AX_PeriodCycleBasis`, arc-level

Date: 2026-06-11. R-lane (worktree `feat/bilinear-relations`). Companion log:
`R2_LANE_PROGRESS.log`. Inputs audited: `Jacobians/Axioms/PeriodCycleBasis.lean`
(the D1 merged axiom, exact field statements), `Jacobians/Layer3/Periods.lean` +
`RiemannBilinear.lean` (consumption: `R1Holds`/`R2Holds` → τ symmetry, `Im τ ≻ 0`,
Siegel), `docs/planning/CYCLEBASIS_ALTERNATIVES.md` (D1 design),
`CUTSURFACE_GAP_ANALYSIS.md` (incl. the C2/§4-flag deep-think verdict),
`KIROV_ROUTE_IDEAS.md` §5, and the port's analytic stack
(`KirovDolbeault/{CutSurface,BoundaryWordR2,BoundaryPositivity,GreenPositivity,
GreenBox,Dissection}.lean`, `Dolbeault/FineResidue/*`, `Dolbeault/FrameTrace.lean`,
`Dolbeault/CechH1CupKill.lean`, `Dolbeault/SerreDuality*.lean`).

---

## 0. What exactly must be proven

The axiom's two Hodge fields, verbatim shapes (`PeriodCycleBasis.lean:220-227`):

```
R1 : ∀ η ζ : HolomorphicOneForm X,
  Q (arcPeriodVec loops η) (arcPeriodVec loops ζ) = 0
R2 : ∀ η : HolomorphicOneForm X, η ≠ 0 →
  0 < (Complex.I * Q (arcPeriodVec loops η) (conjArcPeriodVec loops η)).re
```

over the bundle's own `loops : Fin (2·genus X) → AnalyticLoop X x₀`, with
`arcPeriodVec` = the `(A-periods, B-periods)` split through `αEmbed`/`βEmbed` of
`canonicalArcIntegral`, and `Q ((a,b),(a',b')) = ∑ₖ aₖb'ₖ − bₖa'ₖ`.

**Structural fact that pins every route.** R1/R2 are *not* properties of `X`
alone: a `GL(2g,ℤ)∖Sp(2g,ℤ)` re-indexing of genuine loops violates both
(CYCLEBASIS §0, "hidden role of `symplectic`"). Any honest proof therefore
consumes a *construction-specific comparison input* tying the symplectic
coordinate form `Q` on the chosen loops' periods to an intrinsic analytic
pairing (classically `Q(P(η),P(ζ)) = ∬_X η∧ζ`). The route question is solely:
**which comparison input, and how much of the remainder is provable now.**

The split this lane enforces:

* **Hodge half (R-lane, provable now):** everything from the comparison input
  *down* to the axiom's `∀η ∀ζ` arc-level fields — bilinear collapse to one
  `g×g` block pair, the matrix-level relations, Cauchy/Green analysis.
* **Comparison input (construction side, post-keystone):** the boundary-word
  identities for the actually-constructed loops (slit-sheet / cut data). Stays
  open here; it is the residual content of the eventual general-X discharge
  (CYCLEBASIS Recommendation 4).

## 1. Route verdict: (a′) — abstract boundary-word route (repaired cut-surface), against (b) and (c)

**Chosen: (a′).** State the comparison input as *boundary-word data over our own
arc-period blocks* (the exact shape of the port's proven engines), and prove
R1/R2 fields from it. Reasons:

1. **The analysis is already machine-checked.** The port has, sorry-free and
   compiled in our build (path dep, oleans cached):
   `riemann_R1_of_boundaryWord` (`CutSurface.lean:55` — box Cauchy ⇒ `AᵀB = BᵀA`)
   and `riemann_R2_posDef_of_boundaryWord` (`BoundaryWordR2.lean:131` — Green
   positivity `∬‖h_v‖²>0` ⇒ `i(AᵀB̄−BᵀĀ) ≻ 0`), over
   `boundaryForm_pos`/`greenOnUnitBox`. Only the boundary-word identities and
   nondegeneracy remain as inputs — precisely the construction-specific part.
2. **C2 verdict compliance.** The §4-flag resolution (CUTSURFACE §end) says: the
   *structure* is satisfiable for all g (abstract Gram witness), but the
   *geometric* holomorphic-on-closed-box cut chart is impossible for g ≥ 2
   (angle count `(4g−2)π > 2π`). Consequence adopted here: we do **not** build
   toward a geometric closed-box cut chart; we keep the boundary-word layer
   abstract (hypotheses on `h, F, U`), and record that the eventual geometric
   realization must use the interior-holomorphy weakening (Mathlib's rectangle
   theorems tolerate it) — a port-side refinement of the two engines' `hh`/`hFh`
   hypotheses, *not* a change to anything this lane builds.
3. **D1's own docstring names this route** ("R1/R2 through the port's proven
   boundary-word engine"), and Kirov's independently-factored
   `CanonicalDissection` (`Dissection.lean:83`) carries the same two matrix
   fields — two designs converging on the same interface.

**Rejected (b) — residue route** (`R1` via `∑Res(fω) = 0`, `f` a primitive of
`ω'`): the primitive `f` of a holomorphic form with nonzero periods is
*multivalued on X*; making it single-valued requires the cut surface, so (b) is
the cut-surface argument restated — same comparison input, plus a multivalued
layer Lean lacks. The new unconditional residue atom
(`exists_canonicalData_residueAtom`, `FrameTrace.lean`) sums residues of
*meromorphic* data; it does not touch multivalued primitives. (It is the right
tool for B-4-style lattice nondegeneracy and third-kind reciprocity — different
statements, already other lanes' property.)

**Rejected (c) — Dolbeault/cup-product route**: the intrinsic Hodge facts are
cheap in any formulation (the wedge of two (1,0)-forms vanishes *pointwise*;
`i·η∧η̄ ≥ 0` pointwise), and the port's Čech H¹ + cup (`CechH1CupKill`) + Serre
duality could plausibly express the intrinsic pairing abstractly. But the
challenge fields live on **arc periods of the bundled loops**; transporting the
intrinsic pairing there needs the period isomorphism
`H¹_dR ≅ Hom(H₁,ℂ)` + Poincaré duality/trace on `H²(X,ℂ)` — none of which
exists in the repo or Mathlib, and which re-imports exactly the
intersection-form anchoring problem that D1 removed from the critical path.
In Lean terms (c) is strictly more new infrastructure than (a′) for the same
residual comparison debt.

## 2. Named-lemma decomposition (statement chain)

`P(η) := arcPeriodVec loops η`; blocks over a `Fin (genus X)`-indexed form
family `ω` (row = loop index, column = form index, matching Kirov's
`aPeriodBlock` convention):

```
arcAPeriodBlock loops ω : Matrix (Fin g) (Fin g) ℂ   -- A k i = ∫_{α_k} ω i
arcBPeriodBlock loops ω : Matrix (Fin g) (Fin g) ℂ   -- B k i = ∫_{β_k} ω i
arcPeriodGram   loops ω := I • (Aᵀ·B̄ − Bᵀ·Ā)         -- the period Hermitian form
```

### Layer 1 — linear collapse (Brick 1, `BilinearRelations.lean`, axiom-free)

| # | Lemma | Statement | Input |
|---|---|---|---|
| L1 | `canonicalArcIntegral_sum_smul` | `∫_γ (∑ cᵢ•ωᵢ) = ∑ cᵢ·∫_γ ωᵢ` | `arcPeriodFunctional` linearity + `analyticArc_canonicalIntegrand_intervalIntegrable` (both theorems) |
| L2 | `Q_arcPeriodVec_self` | `Q (P η) (P η) = 0` | `Q` alternating (sum algebra) |
| L3 | `Q_arcPeriodVec_block` | `Q (P (ω i)) (P (ω j)) = (AᵀB − BᵀA) i j` | unfold `Q`, `Matrix.mul_apply` |
| L4 | `Q_arcPeriodVec_sum_smul` | `Q (P (∑cᵢ•ωᵢ)) (P (∑dⱼ•ωⱼ)) = ∑ᵢ∑ⱼ cᵢdⱼ·Q (P ωᵢ) (P ωⱼ)` | L1 + `Finset.sum_mul_sum` + `sum_comm` |
| R1← | `arc_R1_of_blocks` | `AᵀB = BᵀA → ∀ η ζ, Q (P η) (P ζ) = 0` (ω a ℂ-basis of forms) | L3 + L4 + `Basis.sum_repr` |
| g≤1 | `arc_R1_of_genus_le_one` | `genus X ≤ 1 → ∀ η ζ, Q (P η) (P ζ) = 0` | `arc_R1_of_blocks`; `AᵀB = BᵀA` is automatic for 1×1/0×0 blocks (`Subsingleton (Fin g)`) |

### Layer 2 — conjugate/Gram collapse (Brick 2, same file, axiom-free)

| # | Lemma | Statement | Input |
|---|---|---|---|
| L5 | `Q_arcPeriodVec_conj_block` | `Q (P (ω i)) (conjP (ω j)) = (AᵀB̄ − BᵀĀ) i j` | star algebra |
| L6 | `Q_arcPeriodVec_conj_sum_smul` | `Q (P (∑cᵢ•ωᵢ)) (conjP (∑cⱼ•ωⱼ)) = ∑ᵢ∑ⱼ cᵢ·c̄ⱼ·Q (P ωᵢ) (conjP ωⱼ)` | L1 + star of L1 |
| R2← | `arc_R2_of_gram_posDef` | `(arcPeriodGram loops ω).PosDef → ∀ η ≠ 0, 0 < (I·Q (P η) (conjP η)).re` | L5 + L6; `v := star (repr η)`; `Matrix.PosDef` (ComplexOrder) gives `0 < re(vᴴMv)`; `repr η ≠ 0` by basis injectivity |

### Layer 3 — boundary-word feed (Brick 3, `BilinearRelationsBoundaryWord.lean`, imports the port)

| # | Lemma | Statement | Input |
|---|---|---|---|
| F1 | `arc_R1_of_boundaryWord` | port-shape hypotheses (`hFh` + per-entry `(AᵀB−BᵀA) i j = ∮_{∂box} Fᵢ·hⱼ`) over OUR `arcAPeriodBlock/arcBPeriodBlock` → the axiom's R1 field | `riemann_R1_of_boundaryWord` (port, proven) + `arc_R1_of_blocks` |
| F2 | `arc_R2_of_boundaryWord` | port-shape hypotheses (`U`,`hh`,`hF`, conjugated boundary word, `nondeg`) → the axiom's R2 field | `riemann_R2_posDef_of_boundaryWord` (port, proven) + `arc_R2_of_gram_posDef` |
| F3 | `PeriodCycleBasis.ofBoundaryWord` | constructor: loops + `isBasis` + `loops_to_basis` (topology lane's product) + form basis + boundary-word data ⟹ `PeriodCycleBasis X x₀` | F1 + F2 |

F3 is **the consumption point for the future slit-sheet construction**: it makes
"discharge `AX_PeriodCycleBasis`" equal to "produce the H₁ data + the
boundary-word data", with zero remaining Hodge analysis.

## 2b. Status — ALL BRICKS LANDED (2026-06-11, this branch)

| Brick | File | Commit | Kernel closure |
|---|---|---|---|
| 1+2 (L1–L6, R1←, R2←, g≤1) | `Jacobians/RiemannSurface/BilinearRelations.lean` | `a1190ea` | standard-3, all 10 decls |
| g=0 R2 vacuity | same file (`arc_R2_of_genus_eq_zero`) | follow-up | standard-3 |
| 3 (F1–F3) | `Jacobians/RiemannSurface/BilinearRelationsBoundaryWord.lean` | `e8cd5c4` | standard-3, all 7 decls incl. `periodCycleBasisOfBoundaryWord` |

`AX_PeriodCycleBasis` verified ABSENT from every closure (`#print axioms`,
olean-backed). Brick 3 imports only the sorry-free port files
(`KirovDolbeault.CutSurface`, `KirovDolbeault.BoundaryWordR2`); the sorry'd
`CutSurfaceRelations.lean` (`exists_cutSurface`) is NOT imported. Full
`lake build` green with both modules registered in
`Jacobians/RiemannSurface.lean`.

Interface-design note (issue-#82 discipline): `ArcBoundaryWordData` is a
*structure* (hypothesis bundle), not an axiom — no kernel risk; its
satisfiability for g ≥ 2 by a *geometric* witness inherits the C2 verdict's
hh-weakening caveat (§3), deliberately NOT baked into the interface here so
the eventual repair happens port-side without touching these bricks.

## 3. What stays open after the bricks (construction-side, NOT this lane)

* **BW-DATA** — the boundary-word identities + `nondeg` for the constructed
  loops: slit-sheet/cut realization, post-keystone (CYCLEBASIS Direction 2b;
  per-handle integral identity already proven —
  `rectBoundaryIntegral_singleHandle`; the g-handle summed variant is
  hard-but-standard interval algebra *once* the gluing/jump data exists).
* **hh-weakening** — for a *geometric* witness at g ≥ 2 the port engines'
  closed-box holomorphy hypotheses must be relaxed to interior holomorphy +
  boundary continuity (C2 verdict); Mathlib's
  `integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn` and an
  interior-version Green bridge make this a port-side refinement. Do it when
  BW-DATA work starts, not before.
* **H₁ half** (`isBasis`, `loops_to_basis`) — topology lane (T-FG/T-RANK),
  explicitly out of scope here.

## 4. Discipline notes

* No new axioms anywhere in this lane; bricks must be kernel-verified standard-3
  (`#print axioms`), with one documented exception: any corollary that invokes
  the global `FiniteDimensional ℂ (HolomorphicOneForm X)` instance (e.g. to
  *produce* a `Fin (genus X)`-indexed form basis via `Module.finBasis`) picks up
  the two Kirov bridge structural axioms in its closure — such corollaries take
  the basis as explicit data in the main statements and keep instance-using
  wrappers separate.
* `AX_PeriodCycleBasis` must NOT appear in any brick closure (circularity);
  importing `Axioms/PeriodCycleBasis.lean` for `arcPeriodVec`/`αEmbed` is fine —
  closures track uses, not imports — and is verified per brick.
