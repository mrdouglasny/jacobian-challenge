# HANDOVER — parallel-account work packages (2026-06-11)

Self-contained brief for an agent on a **separate account/machine** working this
repo concurrently with the primary orchestrator. Read fully before starting.
Repo: `mrdouglasny/jacobian-challenge`, base everything on `origin/main`.

## Ground rules (non-negotiable)

1. **Read `CLAUDE.md` and `AGENTS.md` at repo root first.** Pre-push Lean
   verification rule (`lake env lean <file>` per touched file; full
   `lake build` before PR), protected-files list, axiom-soundness rules.
2. **NO new `axiom` declarations, ever.** A genuinely unavoidable input becomes
   a named `Prop` hypothesis / structure field, documented in a blocker doc.
   Kernel-verify every headliner with `#print axioms`: expected closure is
   exactly `[propext, Classical.choice, Quot.sound]` ("standard-3") plus only
   explicitly declared named hypotheses. No `sorryAx` in completed work.
3. **Do NOT touch** (active on the primary account, collision risk):
   - branches: `feat/keystone-flip`, `feat/frame-trace-wall`,
     `feat/homology-generation`, `feat/genus0-backward`, `feat/abel-subset`
   - files: `vendor/kirov-dolbeault-port/**` (except read-only),
     `Jacobians/Layer3/**`, `Jacobians/RiemannSurface/{FrameTrace*,GenusZeroBackward,HomologyGeneration,PeriodDiscreteness}.lean`,
     anything under `.github/`, `scripts/axiom_report.lean`,
     `scripts/check_axiom_consistency.sh`, `CLAUDE.md`, `AGENTS.md`
   - The keystone flip (axiom count 21→18) may land mid-flight: rebase on main
     before opening your PR; expect `AXIOM_AUDIT.md`/`README.md` churn — never
     edit the ledger except to reconcile YOUR OWN axiom-count change (here: none).
4. **PR protocol**: branch off main, conventional commits with
   `Co-Authored-By:` trailer per CLAUDE.md, PR body ends with
   "**Estimated human time: 0 minutes.**", no questions to the owner. State
   kernel closures + build job count in the PR body. CI is the final gate.
5. **No new vendoring** of outside code (Kirov or otherwise). Ideas with
   citation OK; implementation ours.
6. Keep a per-session progress log under `docs/planning/<LANE>_PROGRESS.log`
   (append-only) and commit early/often.

## Package 1 (PRIMARY): the S² topology campaign — feeds TWO critical axioms

**Goal A — `SimplyConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)`**
(π₁(S²) = 1; absent from Mathlib at our pin).
Consumer 1 (ready, merged-or-merging as PR #199):
`Jacobians/RiemannSurface/GenusZeroBackward.lean` has
`genus_eq_zero_of_homeo_sphere` taking exactly this as its ONLY hypothesis —
your theorem instantly completes the backward leg of the challenge-critical
`AX_genus_eq_zero_iff_homeo`.

**Goal B — T-FG: `Group.FG (FundamentalGroup X x₀)` for compact `X`**
(π₁ of a compact surface/manifold is finitely generated).
Consumer 2 (PR #198): `Jacobians/RiemannSurface/HomologyGeneration.lean` has
instance `moduleFinite_H1_of_fundamentalGroup_fg`; your theorem feeds the
discreteness half of the challenge-critical `AX_PeriodCycleBasis`
(remaining residual there after T-FG: T-RANK, see stretch goal).

**Route**: the in-repo SVK (Seifert–van Kampen) package `Jacobians/Topology/`
was built for exactly this family — read all of it plus
`docs/planning/SVK*` docs (route + blocker docs name the open rungs, e.g. the
two-open-set SVK statement). For Goal A the classical shape: cover S² by two
contractible opens (complements of poles) with path-connected intersection ⇒
π₁ trivial by SVK. For Goal B: finite good cover (compactness + charts) ⇒
finitely presented π₁ (or use a grid/nerve argument; Goal B may also follow
from Goal A's machinery generalized — scope it honestly).
Mathlib inventory to check first: `SimplyConnectedSpace`,
`FundamentalGroupoid`, anything under `AlgebraicTopology/FundamentalGroupoid/`
(SVK exists there in groupoid form — `FundamentalGroupoid.preserves...` /
pushout statements; check whether the groupoid SVK at our pin can be
specialized instead of building from scratch — that finding alone is valuable).

**Deliverables**: new files under `Jacobians/Topology/` wired into the
umbrella; theorem(s) above kernel-verified standard-3; PR per protocol.
Honest-partial welcome: re-isolate the smallest named gap and prove
everything over it.

**Stretch (only if both goals land): T-RANK** —
`Module.Free ℤ (H1 X x₀)` ∧ `finrank ℤ (H1 X x₀) ≤ 2 * genus X`
(H1 here = the repo's abelianized-π₁ model, see
`Jacobians/RiemannSurface/LoopIntegralHom.lean`). This is
classification-of-surfaces grade; a scoping doc with the minimal lemma chain
is the expected deliverable, not a proof.

## Package 2 (SECONDARY, take only if Package 1 is blocked): Abel ⊆ route doc

`AX_AbelTheorem`'s ⊆ direction (degree-0 divisor with vanishing Abel–Jacobi
image is principal). The ⊇ direction is proven (Liouville route). Planned
route: Forster §20 ∂̄-solvability — BUT the keystone campaign just made Serre
duality a theorem (port-side `SerreDualityData`, `exists_serreDualityData_cover_of_residueAtom`
in `vendor/kirov-dolbeault-port/.../KeystonePackaging.lean`), and ∂̄-solvability
(`∂̄u = η` solvable iff `η ⊥` holomorphic forms) IS Serre duality for `H^{0,1}`.
Deliverable: `docs/planning/AB_ROUTE.md` — the exact decomposition from
`SerreDualityData` fields to the ⊆ statement in
`Jacobians/Axioms/AbelJacobiMap.lean` (read the axiom verbatim), every rung a
named lemma with difficulty class, plus any cheap proven bricks. Work in
`Jacobians/RiemannSurface/AbelSubset*.lean` (root tree), NOT the vendor port
(the primary account owns port edits this week).

## Verification gates (both packages)

- Per-file `lake env lean <file>` after every substantive change.
- Full `lake build` green before PR (expect ~8,700-9,000 jobs; first build
  cold ≈ tens of minutes, cached after).
- `#print axioms` on every headliner, outputs recorded in the lane log.
- `bash scripts/check_axiom_consistency.sh` must pass unchanged (you add no
  axioms, so the count must not move from whatever main says when you rebase).

## Coordination

- Signal = the PR itself; the primary orchestrator reviews/merges with codex
  per the repo's review protocol. Mention `HANDOVER_PARALLEL_ACCOUNT.md` in
  the PR body so it's recognized as handover work.
- If you find an error in merged work, open an issue referencing the pinned
  soundness log (issue #82) — do not push fixes to others' branches.

---

# UPDATE 2 (2026-06-11 late): next packages after #205/#206

Package 1 delivered (#205 merged-or-merging: π₁(S²)=1 + T-FG engine) and the #206
proposal accepted (the primary account's RP-lane is executing the image-lattice
re-plumb — `PeriodDiscreteness.lean` stays primary-owned). Packages 1/2 above are
CLOSED. New no-touch additions: `Jacobians/Bridge/KirovDolbeault*.lean`,
`Jacobians/RiemannSurface/BilinearRelations*.lean`,
`vendor/.../Dolbeault/AbelSubset*.lean` (active primary lanes).

## Package 3 (PRIMARY): genus-0 FORWARD direction → the full
## `AX_genus_eq_zero_iff_homeo` flip

Your #205 made the backward leg unconditional
(`genus_eq_zero_of_homeo_sphere_unconditional`). The forward direction
(genus 0 ⟹ homeomorphic to S²) is now CHEAP because the keystone flip made
its RR input free: **`exists_singleSimplePole_of_genus_zero_of_rr` is
standard-3 on main** (port-side, `KirovDolbeault.RiemannRoch`). Inventory
(from PR #199's body + #205's follow-up notes):
(a) port→main-tree transport of the single-simple-pole existence at genus 0
    (the ℓ(P)=2 pole-extraction analog — port-side proof exists; build the
    main-tree statement against `Jacobians` types, NO new vendoring,
    re-prove against the bridge identifications);
(b) refactor `Jacobians/RiemannSurface/DegreeOneGenusZero.lean` (ownership
    RELEASED to you for this package) so its internal `X ≃ ProjectiveLine`
    becomes an output (`degreeOne_genus_zero` already constructs it with
    `ContMDiff` both ways);
(c) compose with `ProjectiveCurve/Line.lean`'s `onePointEquivSphereOfFinrankEq`
    (ℙ¹ ≃ₜ S²) to land `genus X = 0 → Nonempty (X ≃ₜ Metric.sphere …)`;
(d) THE FLIP: `AX_genus_eq_zero_iff_homeo` axiom → theorem in
    `Jacobians/Axioms/Uniformization0.lean` (statement verbatim), ledger
    16→15 (or current−1), critical−1 — full protocol: kernel re-verify,
    `check_axiom_consistency.sh`, AXIOM_AUDIT + README + axiom-report
    reconcile IN THE SAME PR, body documents closures.
This would be the first challenge-critical axiom fully discharged by the
parallel account.

## Package 4 (SECONDARY/parallel): GC-1 — good-cover existence

Your own `GOODCOVER_BLOCKER.md` GC-1: `SimplyConnectedGoodCover X` for compact
Riemann surfaces (finite cover by simply connected charts with path-connected
pairwise intersections — geodesic balls / chart-disk refinement argument).
Lands `Group.FG (FundamentalGroup X x₀)` unconditionally via your
`fundamentalGroup_fg_of_goodCover`, feeding #198's
`moduleFinite_H1_of_fundamentalGroup_fg` → the discreteness chain.

Same ground rules as above; tag PRs with this file.

---

# UPDATE 3 (2026-06-12): package queue after #209

#209 (package 3, the genus-0 flip) received — under review; ledger may need a
refresh against post-#207 main (16 active / 3 critical) before merge. Package 4
(GC-1) remains open and is still the highest-leverage topology item. Additional
packages, in priority order — pick the next free one, tag PRs with this file:

## Package 5: LineBundle/H1 stub retirement (active-count reduction)

Six of the 16 active axioms are OPAQUE TYPE STUBS, now retirable post-keystone:
`LineBundle` (#65), `H1` + its two instances (#66-#68), `LineBundle.ofDivisor`
(#70) — see their tracker issues + `AXIOM_AUDIT.md` rows. The real objects now
exist: the port's Čech `H1coh`/cohomology (Layer-3, `Jacobians/Layer3/`) and
`riemannRochSpace`-based divisor modules. Work: replace each stub `axiom` with
a real `def` against the existing machinery (the pattern = #201's
`canonicalDivisor` de-opaque: keep fully-qualified names, consumers must
elaborate unchanged), flip `AX_RiemannRoch`/`AX_SerreDuality` (#37/#38) to
theorems over the de-opaqued types if their statements then close (they are
already standard-3 + stubs-only). Ledger: each retirement −1 active, full
reconcile per protocol IN THE SAME PR (do them in one PR or per-stub PRs,
your call; kernel count from `scripts/check_axiom_consistency.sh` each time).
Files: `Jacobians/RiemannSurface/Cohomology/LineBundleBasic.lean` + consumers
(grep each stub name first; statement-preservation is the whole game).
Potential: active 16 → 10.

## Package 6: Abel A-block plumbing (root-side, engine-agnostic)

The Abel ⊆ campaign's root-side assembly, written against NAMED ENGINE OUTPUTS
as hypotheses (the port-side engine is primary-owned and in flight — your work
must not import the AbelSubset* port files, only STATE the bridge):
read `docs/planning/AB_ROUTE.md` A-block rungs. Deliverable: 
`Jacobians/RiemannSurface/AbelPlumbing.lean` — (A1) unfold `AX_AbelTheorem`'s
⊆ statement (Jacobians/Axioms/AbelJacobiMap.lean — read verbatim) to the
divisor/period-lattice shape; (A2) the divisor bridge (degree-0 divisor ↦ the
data the engine consumes); (A3) the assembly theorem: [named hypothesis: the
§20 solvability/Weierstrass output] → the ⊆ statement. All standard-3 +
named hypotheses; NO AX_AbelTheorem in closures.

## Package 7: existing work-package issues

GitHub issues #171 (π₁ of punctured sphere is free — SVK-lite, feeds the
PeriodCycleBasis topology stack) and #172 (hyperelliptic PeriodCycleBasis
witness via branch-cut loops) are pre-scoped work packages from the main
program — fair game, root-side, same rules.

Active primary lanes (no-touch refresher): `vendor/.../Dolbeault/AbelSubset*`,
`Jacobians/Bridge/KirovDolbeault*`, `Jacobians/RiemannSurface/{BilinearRelations*,PeriodDiscreteness}.lean`.
