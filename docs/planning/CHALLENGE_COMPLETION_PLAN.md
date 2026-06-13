# Challenge completion plan

*2026-06-12. Kernel-verified baseline: HEAD `399a243`.*

## Current state

`docs/axiom-report.txt` at HEAD shows exactly **2 custom axioms** reachable
from any Buzzard obligation:

| Axiom | Buzzard declarations affected |
|---|---|
| `AX_PeriodCycleBasis` | **ALL 23** (every Jacobian declaration except `genus_eq_zero_iff_homeo`) |
| `AX_AbelTheorem` | `Jacobian.ofCurve_inj` only |

`genus_eq_zero_iff_homeo` was discharged by PR #209 today: standard-3.
Cluster C is fully discharged (#31). `AX_PlaneCurveAffine_connected` appears
only in the non-Buzzard `PlaneCurve.instConnectedSpace`; ignore for this plan.

**Goal:** discharge both axioms → every Buzzard declaration prints
`[propext, Classical.choice, Quot.sound]`.

---

## Out of scope (do not touch for challenge closure)

Distracts from the goal; tracked separately in the ledger:

- Albanese UP axioms (4): `AX_torus_oneforms_dualCover`, `AX_torus_self_albanese`,
  `AX_period_functoriality`, `AX_curve_generates_jacobian`
- RR/Serre stubs (5): `LineBundle`, `LineBundle.ofDivisor`, `H1`, its two
  instances, `AX_RiemannRoch`, `AX_SerreDuality`
  *(Package 5 from HANDOVER_PARALLEL_ACCOUNT.md can retire these
  as a side-campaign; they reduce active count without touching the 2 critical)*
- Intersection form laws (2): `AX_IntersectionForm_alternating/perfect`
- Plücker formula (1): `AX_PluckerFormula`
- Concrete curve witnesses: `AX_Elliptic_H1_symplectic`,
  `AX_PlaneCurveAffine_connected`

---

## Axiom 1: `AX_PeriodCycleBasis` — the structural keystone

**Statement** (`Jacobians/Axioms/PeriodCycleBasis.lean:237`):
every compact connected Riemann surface has a `PeriodCycleBasis X x₀`:
```
loops       : Fin (2g) → AnalyticLoop X x₀
isBasis     : Module.Basis (Fin 2g) ℤ (H1 X x₀)
loops_to_basis : ∀ i, isBasis i = loopToHomology (loops i)   -- Hurewicz tie
R1 : ∀ η ζ, Q (arcPeriodVec loops η) (arcPeriodVec loops ζ) = 0
R2 : ∀ η ≠ 0, 0 < Re(i · Q(arcPeriodVec loops η, conjArcPeriodVec loops η))
```

### What is already proved (PR #203 + prior)

`BilinearRelationsBoundaryWord.lean` establishes the **full Hodge reduction**:

```
ArcBoundaryWordData loops cω   →   PeriodCycleBasis X x₀
    (via periodCycleBasisOfBoundaryWord, sorry-free)
```

`ArcBoundaryWordData` requires `h`, `F`, `U` and two boundary-word identities
over OUR arc-period blocks. The analysis side (R1 from box-Cauchy, R2 from
Green positivity) is **done**; the port's
`riemann_R1_of_boundaryWord` + `riemann_R2_posDef_of_boundaryWord` are
sorry-free and compiled. **Zero Hodge theory remains open at this layer.**

`PeriodDiscreteness.lean` (PR #208) establishes lattice discreteness under the
named hypothesis `PeriodGeneratingLoops x₀ b γs`:
every closed analytic loop's period vector lies in the ℤ-span of the
family's 2g period vectors → lattice is discrete, is a ℤ-lattice, has a
ℤ-basis. This is the "topology lane" interface that a homology-basis
construction must satisfy.

### What remains (the two open inputs)

**Input A — `ArcBoundaryWordData` for our loops (the cut-surface
construction):**
Need a geometric realization of the boundary-word data for a specific family of
2g loops on an arbitrary genus-g Riemann surface. Classically this is the
fundamental-polygon / slit-sheet construction (Forster §§17–19, the 4g-gon).

The Kirov port has `CanonicalDissection` (`Dissection.lean:83`) carrying the
same two matrix fields — a design that converges on the same interface.
The C2 verdict says the *closed-box* holomorphy hypothesis in the port's engines
must be weakened to interior-holomorphy + boundary-continuity for genus ≥ 2
(a port-side refinement). This is a known, scoped refinement, not a
redesign.

**Status:** open. Issue #172 (hyperelliptic PeriodCycleBasis witness via
branch-cut loops) and `docs/planning/SVK_ROUTE.md` / `CUTSURFACE_GAP_ANALYSIS.md`
have the scoping. The construction is the single remaining hard piece on
the PCB side.

**Input B — `isBasis` + `loops_to_basis` (H₁ topology):**
A ℤ-basis of `H1(X, x₀) = Additive (Abelianization (FundamentalGroup X x₀))`
indexed by `Fin (2 * genus X)`, with the Hurewicz tie.

`PeriodGeneratingLoops` is the interface: once the cut-surface construction
produces a family of 2g loops whose period vectors span the lattice, this
hypothesis is satisfied and `PeriodDiscreteness.lean` closes the discreteness
side.

The rank count (rank 2g) requires `Group.FG (FundamentalGroup X x₀)` (T-FG
from Package 1 of HANDOVER) and the classification of surfaces (or the
chain-complex rank argument). Issue #171 (π₁ of punctured sphere is free) and
#172 are pre-scoped here.

**Status:** `Group.FG` route is in progress (Package 1, topology lane, PR #198
merged `HomologyGeneration.lean`). T-RANK (rank = 2g) is the stretch; scoped
in the handover but not yet proved.

### Discharge path for `AX_PeriodCycleBasis`

```
1. (Topology lane) Prove: ∃ family of 2g analytic loops that form a ℤ-basis
   of H₁ with the Hurewicz tie and satisfy PeriodGeneratingLoops.
   → inputs: T-FG (in progress), T-RANK (scoped, issue #172 likely the
     hyperelliptic witness; the abstract argument needs classification-of-surfaces
     or its cut-surface corollary).

2. (Construction lane) Prove: those loops admit an ArcBoundaryWordData.
   → the slit-sheet / 4g-gon construction; adapts the port's CanonicalDissection
     with the closed-box → interior-holomorphy weakening (scoped as a port
     refinement).

3. Instantiate periodCycleBasisOfBoundaryWord with those two inputs.
   → zero further analysis: this step is proved in BilinearRelationsBoundaryWord.lean.
```

**Hard bottleneck:** steps 1–2 are topological + analytic construction work
(the 4g-gon / fundamental polygon). No Lean proof of this construction exists
anywhere yet. Estimated effort: substantial (weeks), dependent on how much of
the Kirov port's `CanonicalDissection` is portable and how quickly the rank
count can be established.

---

## Axiom 2: `AX_AbelTheorem` — two halves, one in flight

**Statement** (`Jacobians/Axioms/AbelTheorem.lean:80`):
```
(abelJacobiDiv X).ker ⊓ (Divisor.deg X).ker = PrincipalDivisors X
```
Degree-0 divisors with vanishing Abel–Jacobi image = principal divisors.

### ⊇ direction: principal ⊆ kernel (Abel necessity)

Route: Liouville / Cauchy argument — if `f` is meromorphic with divisor D,
`AJ(D) = 0` by period cancellation. PR #204 opened the ∂̄-criterion from
Serre duality and the third-kind differential existence (9 bricks proved,
S-block + TK0/TK1). AB_LANE_PROGRESS.log shows this is in active development
on the primary lane.

**Status:** significant infrastructure landed; the assembly (proving
`PrincipalDivisors X ≤ (abelJacobiDiv X).ker`) has not yet appeared as a
proved theorem. The ⊇ direction is **closer than ⊆** but not yet closed.

### ⊆ direction: kernel ⊆ principal (Jacobi inversion / sufficiency)

Route A (chosen per AB_ROUTE.md): Forster §20 ∂̄-engine via SerreDualityData.
Given that `SerreDualityData` is now a theorem (post-keystone), the route is:

```
σ = ∂̄u solvable  ⟺  ∫_X σ∧ω = 0 for all ω ∈ H^{1,0}
```

This is Serre duality for H^{0,1}, now available as `exists_serreDualityData_cover`.
The dimension count (`dim_ℝ H^{0,1}_∂̄ = 2g`, comparison transport) is proved
(PR #204, `AbelSubsetCriterion.lean`). Remaining rungs per AB_ROUTE.md:

- **P-block (pairing):** P1 (zeroOneCoeff chart read) → P2/P3 (pairing through
  `FineResidue.resIntegral`) → P4 (Stokes kill: period functional kills im ∂̄) →
  P5 (Gram surjectivity: positivity of ∫ω̄∧ω) → P6 (assembled §19.10 criterion).
- **TK2 (third-kind, residue):** opposite residues at both poles via the residue
  atom `exists_canonicalData_residueAtom`.
- **E-block (§20 engine):** weak solution — given a (0,1)-form σ with all periods
  zero, solve for u with ∂̄u = σ; this is the §20 solvability proper.
- **Assembly:** connect the weak solution to the meromorphic-function-existence
  step (the map `D ↦ f` with `div f = D`), and close the kernel equality.

**Status:** the criterion infrastructure (S-block, TK0/TK1) is proved. The
P-block and E-block are the next active bites in the primary lane. This is a
deep, multi-week campaign; the Kirov port's `AbelSubset*.lean` files are the
primary implementation work.

### Assembly

The ⊇ and ⊆ directions are independent; whichever lands first can be shipped
separately as a tighter axiom (e.g. just ⊆, or just ⊇) if that reduces
challenge-facing `sorry`. But `ofCurve_inj`'s proof uses the full equality —
check `Jacobians/Axioms/OfCurveInjective.lean` to see if it needs the full
biconditional or only one half.

Package 6 from the handover (Abel A-block plumbing) can be done on a parallel
account: write `Jacobians/RiemannSurface/AbelPlumbing.lean` that unfolds
`AX_AbelTheorem`'s ⊆ statement to the engine's output format, stated as
named hypotheses (no `axiom`). This creates the "last mile" plumbing so that
whenever the port's engine lands, it plugs in immediately.

---

## Work ordering

```
Parallel tracks (both can proceed independently):

Track A — PeriodCycleBasis
  A1: T-FG (Group.FG, package 1) — topology lane, in progress
  A2: T-RANK (rank = 2g) — next topology item after A1
  A3: ArcBoundaryWordData construction — slit-sheet/4g-gon, main campaign
  A4: instantiate periodCycleBasisOfBoundaryWord — trivial once A1–A3 land

Track B — AbelTheorem
  B1: Abel A-block plumbing (package 6) — parallel-account, near-term
  B2: P-block (pairing bricks P1–P6) — primary lane, in flight
  B3: TK2 (third-kind opposite residues)
  B4: E-block (§20 weak-solution engine) — primary lane
  B5: ⊇ direction assembly
  B6: full AX_AbelTheorem flip

Bottlenecks:
  A3 (slit-sheet) is the HARDEST and the rate-limiter for Track A.
  B4 (§20 engine) is the HARDEST and the rate-limiter for Track B.
  Both are independent of each other: A3 completion doesn't unblock B4,
  and B6 doesn't help A3.
```

If Track B completes first (`AX_AbelTheorem` discharged), the only remaining
Buzzard non-closure is `ofCurve_inj` — 22 of the 24 declarations become
standard-3. If Track A completes first (`AX_PeriodCycleBasis` discharged),
all 23 become standard-3 except `ofCurve_inj`. Full closure requires both.

---

## Checks on this plan

**Open questions worth verifying before execution:**

1. **Does `Jacobian.ofCurve_inj` need the full biconditional `AX_AbelTheorem`,
   or only one half?** If it only needs the ⊆ direction, Track B can target
   ⊆ only first, which is slightly less work than the full equality.
   *Check `Jacobians/Axioms/OfCurveInjective.lean`.*

2. **Is the H₁ ℤ-basis (T-RANK) actually needed separately, or does it follow
   from the cut-surface construction?** The 4g-gon construction produces 2g
   explicit loops; their homology classes being a ℤ-basis of `H₁` is a
   separate topological fact (van Kampen + abelianization + rank). It's
   likely bundled with the construction, but the proof obligation must be
   explicit.
   *Check what `periodCycleBasisOfBoundaryWord` requires as `isBasis`.*

3. **Is the closed-box → interior-holomorphy weakening of the port engines
   a straightforward localization or does it need new analytic theory?**
   If straightforward, the C2 flag is a minor obstacle. If it requires, e.g.,
   a version of the Schwarz reflection principle or boundary Cauchy theory not
   in Mathlib, it could gate the slit-sheet construction significantly.
   *Check `KirovDolbeault/CutSurface.lean` hypothesis shapes.*

4. **Is `riemann_R2_posDef_of_boundaryWord` actually sorry-free at the
   current Mathlib pin?** The route doc says yes; verify against the compiled
   port.
   *`lake build KirovDolbeault.BoundaryWordR2` or `#print axioms` on the theorem.*

5. **Can the `AX_AbelTheorem` ⊇ direction be proved independently from the
   Liouville/Cauchy route without going through the §20 engine?** The Liouville
   route (ABEL_SUPSET_LIOUVILLE_ROUTE.md) may be shorter than the ∂̄ route for
   ⊇ — check whether it's been abandoned or just not yet started.

---

# POST-MERGE STATUS + EXECUTION (2026-06-12, after #210/#213/#214)

Ledger: **13 active / 2 challenge-critical** (#210 retired the RR/Serre stubs).
The plan above remains the map; state advances and question answers:

## Question answers (verified)

1. **`ofCurve_inj` needs ⊆ ONLY** (verified: `OfCurveInjective.lean:34` rewrites
   `⟨hAJ, hdeg⟩` INTO `PrincipalDivisors` via `← AX_AbelTheorem`). The
   challenge-critical content of Track B is exactly the ⊆ campaign in flight.
   The full-equality flip still wants ⊇ (Liouville), which the E-block's
   chain/period vocabulary makes near-free (div f = ∂c ⟹ chain periods vanish);
   schedule ⊇ as a rider on the E-block completion, flip the equality once.
4. `riemann_R2_posDef_of_boundaryWord` sorry-free: re-confirmed (#203 review +
   compiled imports).
5. ⊇ Liouville: NOT in-tree (route doc only — AB_ROUTE §0 flag); superseded by
   the E-block rider above.

## Track B (AbelTheorem) — ahead of the doc

- P-block COMPLETE (#213 merged): `dbar_solvable_of_pairOmega_eq_zero`
  unconditional standard-3 (P1-P6 incl. Stokes kill + Gram surjectivity).
- E-block OPENED (#215, in review): E0/E1/E2/E5 proven — the assembly
  `exists_meromorphic_of_zeroPeriodChain` done through P6. REMAINING (AB-E2
  lane in flight): E3 (LogDbarDatum constructor, Forster 20.5 slit toolkit
  landed), E4 (pairing field), W1/W2 (walls; W1 core in-tree), E6 (open-path
  developingValue↔lineIntegral + the #211 adapter).
- #211 (A-block plumbing) pre-verified CLEAN, awaiting external review.
- On E3-E6 + #211 + ⊇-rider: **the AX_AbelTheorem flip** (critical 2→1).

## Track A (PeriodCycleBasis) — lattice side closed, construction is the wall

- TR-DISC closed over the datum (#214): residual stack = exactly
  {ArcBoundaryWordData} + {PeriodGeneratingLoops}.
- **A3 (the wall): ArcBoundaryWordData construction — KIROV'S APPROACH IS THE
  ROUTE**: the port's `CanonicalDissection` (Dissection.lean:83) carries the
  same matrix fields and is ALREADY VENDORED (usable directly, not new
  vendoring); the C2-flagged closed-box→interior-holomorphy weakening of the
  port engines is the scoped refinement. First task: the BW-scout brief
  (gap analysis port-engines ↔ our datum + the g=1 explicit-square witness +
  the #172 hyperelliptic branch-cut witness as the family-level partial).
- Input B (topology): other machine — T-FG via GC-1 (#212's G-ladder G1/G2/G3-half
  landed), T-RANK next; #198's interface ready.

## Execution assignments

- AB-E2 lane (running): E3/E4/W1/W2/E6 → the ⊆ chain end-to-end + the ⊇ rider.
- BW lane (next free slot): A3 scoping → g=1 witness → CanonicalDissection
  adaptation campaign.
- Other machine: #211/#212 to merge (reviews pending), then GC-1 (package 4)
  + T-RANK; packages refreshed in HANDOVER doc as needed.
- Maintainer loop: merges, reviews, kernel verification, ledger, flips.

Bottlenecks unchanged: A3 (slit-sheet/dissection) and E3-E6; both active.

---

# SCOPE CORRECTION (2026-06-12 night): family witnesses are NOT all cheap

The HW lane (#231) established by honest determination + Gemini cross-check:
the **hyperelliptic** boundary-word walls (R1Word/R2GramWord) are research-grade,
NOT a quick family win. `BranchCutSystem` carries no symplectic/intersection
data, so R1Word is *algebraically false* for arbitrary loops; an honest
discharge needs concrete `x^k dx/y` period computation over branch cuts (Route K
or via AX_Hyperelliptic_genus). The g=1 elliptic witness (#225/#228, DONE) closed
only because the 1×1 period product commutes — it does not generalize cheaply.

**Consequence for the endgame**: the CRITICAL PATH does **not** route through
family witnesses. It is:
  K-LITE (dissection-free DiscreteTopology, Kirov 21.4 route) → #230's H1
  composite consumes {T-GEN, T-FG, Module.Free ℤ H1, T-RANK(≤)} → the general
  AX_PeriodCycleBasis flip (with the R1/R2 fields handled by either keeping them
  as the general boundary-word obligation, or the K-MID drop, Discussion #229).
The hyperelliptic family witness is a SEPARATE demonstration program, not a
flip prerequisite. The Cholesky + polarization rungs (#231) are banked for it.
