# The last axiom of the Jacobian challenge: precise statement of the remaining issue, and the options

*Prepared for an external review (deep-think). Self-contained; assumes only
standard Riemann-surface theory, not our codebase.*

## 0. One-paragraph summary

We have a Lean 4 / Mathlib formalization of the Jacobian of a compact connected
Riemann surface `X` of genus `g`, addressing Buzzard's "Jacobian Challenge" (24
required properties of the Jacobian and the Abel–Jacobi map). All 24 are proved
**sorry-free**. Their kernel closure depends only on the three standard Lean
axioms (`propext`, `Classical.choice`, `Quot.sound`) **plus a single project
axiom**, `AX_PeriodCycleBasis`, which survives in `ofCurve_inj` (injectivity of
Abel–Jacobi for `g>0`) and the functoriality headlines. We have determined,
kernel-verified, that this lone axiom reduces **exactly** to one classical fact —
call it **T-GEN** — and that T-GEN is Mathlib-absent and (by the route we took)
hard. The question is whether T-GEN is genuinely required, or an artifact of our
construction that a different (also standard) construction avoids. We want an
expert judgement on which of the options below is correct/best.

## 1. The mathematics (no Lean)

Fix a compact connected Riemann surface `X`, genus `g`, basepoint `x₀`. Let
`Ω = H⁰(X, Ω¹)` be the `g`-dimensional space of holomorphic 1-forms. The period
pairing is `H₁(X, ℤ) × Ω → ℂ`, `(γ, ω) ↦ ∮_γ ω`. Choosing a basis of `Ω`
identifies `Ω* ≅ ℂ^g`, and the **period lattice** is the image
`Λ = { (∮_γ ω₁, …, ∮_γ ω_g) : γ ∈ H₁(X,ℤ) } ⊆ ℂ^g`. The **Jacobian** is
`J = ℂ^g / Λ`, and **Abel–Jacobi** is `u : X → J`, `u(P) = (∮_{x₀}^P ω_i)_i mod Λ`.

Classically, `Λ` is a full-rank (`rank 2g`) discrete lattice — two facts:
- **(D) discreteness:** `Λ` is discrete in `ℂ^g`.
- **(N) non-degeneracy / full real span:** `span_ℝ Λ = ℂ^g` (equivalently the
  period pairing is non-degenerate: a holomorphic form with all periods zero is
  zero, by the maximum principle on its single-valued primitive).

Given (D)+(N), `J` is a complex `g`-torus and `u` is a holomorphic embedding for
`g>0` (Abel's theorem). None of this is in question mathematically; the issue is
purely about what a *formal proof in our specific setup* requires.

## 2. The Lean situation: two period lattices, and the gap between them

Our development contains **two** realizations of the period lattice, and the
gap between them is the entire remaining issue.

### (A) The *analytic-loop* lattice `loopPeriodLattice` — fully proved, axiom-free
`loopPeriodLattice := ℤ-span { period vector of γ : γ an analytic loop }`.
We have proved, with kernel closure exactly `[propext, Classical.choice,
Quot.sound]` (no project axiom):
- `discreteTopology_loopPeriodLattice` — (D), via an isolated-zero/residue
  argument (Forster 21.4(b)). **Crucially, this argument is chart-local on the
  holomorphic *forms*, not on the loops**; loop-analyticity is not used in the
  discreteness proof itself.
- `span_real_loopPeriodLattice_eq_top` — (N), via the maximum principle
  (Forster 21.4(c)).
- `isZLattice_loopPeriodLattice` — hence `loopPeriodLattice` is a full-rank
  discrete ℤ-lattice, unconditionally and axiom-free.

### (B) The *continuous-loop* lattice `periodLatticeInBasis` — what the headlines use
Our `Jacobian` and `ofCurve` were constructed (a refactor we call REFOUND) on
the **Hurewicz tower**: `H₁ := Additive(Abelianization(π₁(X, x₀)))`, with the
period map defined on this `H₁` of **continuous** loops. The headline lattice is
`periodLatticeInBasis := range (period map on H₁)`. `ofCurve_inj` and the
functoriality headlines are stated about the Jacobian `ℂ^g / periodLatticeInBasis`,
so their kernel closures reference (B), not (A).

### The bridge — and where the axiom lives
There is a comparison `loopPeriodLattice_eq_periodLatticeInBasis`:
- `loopPeriodLattice ⊆ periodLatticeInBasis` — **axiom-free** (an analytic loop
  is in particular a continuous loop).
- `periodLatticeInBasis ⊆ loopPeriodLattice` — **requires `AX_PeriodCycleBasis`**,
  and is provably *equivalent* to:

> **T-GEN** (`AnalyticLoopsGenerateH1`): the classes of analytic loops
> ℤ-generate `H₁(X,ℤ)` — equivalently, every continuous loop is homotopic to an
> analytic loop.

This reverse inclusion is the **sole** route by which `AX_PeriodCycleBasis`
enters `ofCurve_inj`: the only thing the headlines actually need from the axiom
is that `periodLatticeInBasis` is discrete and full-rank, and the only obstacle
to deducing that from the already-proved (A) is `periodLatticeInBasis ⊆
loopPeriodLattice` = T-GEN. (We separately confirmed the headlines do **not**
need the Riemann bilinear relations / polarization — only (D)+(N) of the lattice
they are built on.)

We have built, kernel-verified, all the `…_of_tgen` lemmas: assuming T-GEN, every
downstream obligation (the discreteness instance, Abel's theorem via a basis-free
adapter, the Liouville step `fiberAJ_eq`) closes to standard-3. So **the entire
remaining `AX_PeriodCycleBasis` dependency of the challenge equals T-GEN.**

## 3. Why T-GEN is hard *here*

We reduced T-GEN (kernel-verified) to two classical approximation theorems, both
**absent from Mathlib**:
- **Whitney:** every continuous loop is homotopic rel endpoints to a smooth loop.
- **Grauert / Whitney–Bruhat:** every smooth loop is homotopic rel endpoints to
  a real-analytic loop (on a real-analytic manifold).

These are true and standard, but formalizing them needs differential-topology
infrastructure Mathlib lacks (manifold-codomain smooth approximation; no
real-analytic partition of unity — the identity theorem blocks the naive glue;
real-analytic tubular neighborhoods). We estimate a multi-week build-out.

### 3.5 Candidate escape (under active verification): *piecewise*-linear approximation

**This may dissolve §3 entirely, and is the route we now consider most likely.**
Our `AnalyticLoop`/`AnalyticArc` is **piecewise**-analytic: analyticity is required
only on the open cells of a finite partition, with **corners allowed** at the
partition points. We do *not* need globally-smooth or globally-analytic loops.

Consequently a **piecewise-linear-in-charts** loop (each piece a straight segment
in a chart's ℂ-coordinate) is already an `AnalyticLoop`: a segment is real-analytic
(degree-1 polynomial), and stays real-analytic read through any other chart
(holomorphic transitions); corners sit at partition points. And every *continuous*
loop is homotopic rel endpoints to such a PL loop by an **elementary** argument —
cover by chart balls, take a Lebesgue number, subdivide so each piece lies in one
convex ball, replace each piece by the chart-segment — where each replacement is
the *already-proved* chart-local straight-line homotopy (`Path.homotopic_of_extChartLocal`),
chained (`Path.homotopic_of_chain`). This discharges T-GEN **avoiding both walls**:
no Whitney (corners are fine, so no smoothing needed) and no Grauert (piecewise,
so no global real-analytic structure / no partition of unity needed). The two §3
theorems were artifacts of over-constraining the approximation target to
corner-free smooth / corner-free global-analytic.

**Status:** being prototyped now (branch `feat/tgen-pl-approx`). The one point to
verify in our formalization is that a PL-in-charts arc genuinely satisfies our
`IsAnalyticArcStrong` predicate (the moving-chart witness machinery) and that the
Lebesgue/convex-ball bookkeeping formalizes cleanly. **Review question (high
priority): is this PL route mathematically correct and does it genuinely avoid
the Whitney/Grauert content, or is there a subtlety that forces smoothing after
all?** If correct, options P1/P2/P3 below are mostly moot — the answer is "prove
T-GEN, elementarily, via PL approximation."

## 4. The crux: is T-GEN actually necessary?

Here is the tension, and the reason for this review.

T-GEN is forced **only because** our `ofCurve`/`Jacobian` are built on the
continuous-loop object `H₁ = Abelianized π₁` (the (B) lattice). The mathematics
of §1 never needs "analytic loops generate `H₁`": it needs only (D)+(N) of *some*
realization of `Λ`, and we already have (D)+(N) for the analytic-loop realization
(A), axiom-free.

Concretely: `loopPeriodLattice` (A) is already a proven full-rank discrete
lattice, and `periodLatticeInBasis` (B) ⊇ (A). Without T-GEN we cannot conclude
(B) is discrete (a priori (B) could be a strictly finer, even dense, subgroup).
So the difficulty is entirely that the headlines are phrased over (B) rather than
(A).

**Independent evidence that an alternative avoids T-GEN.** A separate,
independently-developed solution to the same challenge (Kirov, kernel-replayed by
an external comparator to be **sorry-free and axiom-free**, depending only on the
three standard Lean axioms) constructs the Jacobian *differently*: its period
lattice is the ℤ-span of periods of all **smooth** loops, `ofCurve` is defined via
smooth **paths**, and it **never forms an abstract `H₁` / `Abelianized π₁`
object**. It proves (D) and (N) directly on that smooth-loop lattice (the same
Forster 21.4(b),(c) arguments we use for (A)), and obtains `ofCurve_inj` via
Abel's theorem — with **no T-GEN, no Whitney, no Grauert**. So at least one
standard construction of the Jacobian satisfies all 24 properties axiom-free
without T-GEN.

## 5. The options

- **P1 — Keep our construction; prove T-GEN.** Discharge Whitney + Grauert
  (multi-week, Mathlib-absent). Everything else is already proved and wired
  (the `…_of_tgen` lemmas), so the challenge auto-closes the moment T-GEN lands.
  Resulting state if not yet done: "axiom-free modulo one named, standard
  classical approximation theorem."

- **P2 — Re-architect `ofCurve`/`Jacobian` onto the smooth-loop (or analytic-loop)
  lattice**, i.e. build the headlines over realization (A) (which is already a
  proven axiom-free lattice) instead of (B), defining Abel–Jacobi via paths
  rather than via `Abelianized π₁`. This is essentially Kirov's architecture,
  and (by his comparator-clean result) avoids T-GEN entirely. Cost: a core
  redefinition of the Jacobian and Abel–Jacobi map, partly reversing REFOUND.

- **P3 (candidate — needs adjudication) — Prove (D)+(N) directly on the
  continuous-loop lattice (B), without the bridge.** Since the discreteness
  argument for (A) is "chart-local on the forms, not on the loops," it is not
  obviously specific to analytic loops. *Question:* is the developing potential /
  period functional well-defined and isolated-zero-bounded for **continuous**
  loops, so that `discreteTopology(periodLatticeInBasis)` and its full rank can
  be proved directly — bypassing both T-GEN and any re-architecture? If yes, this
  is by far the cheapest route. If the argument secretly needs a smooth/analytic
  representative to evaluate the integral, P3 collapses back into T-GEN.

## 6. Questions for review

1. **Is the reduction correct?** Do you agree that, in a construction where the
   Jacobian is `ℂ^g / (continuous-loop period lattice)`, formal injectivity of
   Abel–Jacobi genuinely requires identifying that lattice with the
   analytic/smooth-loop lattice (= T-GEN), absent some other input?

2. **Is T-GEN avoidable in principle (P3)?** The discreteness of `Λ` follows from
   an isolated-zero argument on the period functional. Is that functional
   meaningfully defined and bounded on *continuous* loops (e.g. via a developing
   map / single-valued primitive that exists once periods are constrained),
   allowing (D)+(N) to be proved on the continuous-loop lattice directly — without
   ever proving "analytic loops generate `H₁`"? Or is some regularity
   (smoothing) of the loop unavoidable to even define/bound the integral, forcing
   a Whitney-type step?

3. **Is the homology-side vs form-side non-degeneracy the right lever?** We have
   form-side non-degeneracy (a form with zero periods is zero). For Abel–Jacobi
   injectivity over (B) we seem to need homology-side control (the period map on
   `H₁` is injective with full-rank discrete image). What is the minimal
   non-degeneracy statement that suffices for `ofCurve_inj`, and is it provable
   from form-side non-degeneracy + the topological fact `H₁(X,ℤ) ≅ ℤ^{2g}`
   without T-GEN?

4. **P1 vs P2 recommendation.** Given (a) T-GEN = Whitney+Grauert is multi-week
   Mathlib-absent but a single well-understood theorem with everything else
   wired, vs (b) the smooth-loop re-architecture is known to work (Kirov) but is
   a major core redefinition that converges our independent development toward
   his — which is the better investment? Is there a standard textbook route to
   Abel–Jacobi injectivity that sidesteps exhibiting or generating a homology
   basis altogether and would localize the remaining work better than either?

5. **Anything we are missing** — a fourth option, or a reason the framing above
   is subtly wrong.

## 7. Pointers (for anyone checking against the code)

- Axiom: `Jacobians.Axioms.AX_PeriodCycleBasis`.
- Headline: `Jacobians.Jacobian.ofCurve_inj` (`Jacobians/Challenge.lean`).
- Proved axiom-free (A): `span_real_loopPeriodLattice_eq_top`,
  `discreteTopology_loopPeriodLattice`, `isZLattice_loopPeriodLattice`
  (`Jacobians/RiemannSurface/PeriodDiscreteness*.lean`).
- Bridge: `loopPeriodLattice_eq_periodLatticeInBasis`
  (`Jacobians/.../Layer3/.../PeriodLatticeDiscrete.lean`); reverse inclusion = T-GEN.
- T-GEN: `AnalyticLoopsGenerateH1`; reduction to {Whitney, Grauert} in
  `Jacobians/RiemannSurface/TGenFinalReduction.lean`
  (`SmoothLoopApproxHyp`, `SmoothLoopAnalyticApprox`).
- `…_of_tgen` wiring + kernel evidence: branch `feat/path2-prototype`,
  `Jacobians/RiemannSurface/Path2Prototype.lean`,
  `docs/planning/path2-evidence/AXIOM_OUTPUT.txt`.
- Kirov reference construction: `../jacobian-claude` (`truePeriodLattice`,
  `PeriodLattice/PeriodLatticeNondegenerate.lean`,
  `PeriodLattice/PeriodLatticeDiscrete.lean`, `smoothPath`).

## 8. Review verdict (deep-think, 2026-06-13)

**The PL route (§3.5) is correct and is the definitive path. Pursue P1 executed
via PL approximation. P2 and P3 are dropped.**

- **PL is mathematically bulletproof.** Whitney/Grauert are needed in the
  literature only to produce *corner-free* (globally smooth / globally analytic)
  loops. `AnalyticLoop` is piecewise-analytic with corners allowed, so that
  global regularity is never required. An affine segment is real-analytic, and
  holomorphic transitions preserve it. The Lebesgue + convex-ball argument is the
  standard textbook bridge from continuous topology to integration.
- **T-GEN (A = B, index 1) is genuinely required (Q1 confirmed).** Form-side
  non-degeneracy + `H₁ ≅ ℤ^{2g}` only give that `Λ_A` is a *finite-index*
  subgroup of `Λ_B`. Finite index is insufficient for `ofCurve_inj`: a proper
  quotient `J_A ↠ J_B` could fold distinct curve points separated by a fractional
  period. Only homology-side surjectivity (T-GEN, index 1) rules this out. So we
  cannot skip T-GEN — but PL *proves* it elementarily.
- **P3 is an illusion (Q2 confirmed).** Evaluating `∮_γ ω` for an arbitrary
  continuous loop forces breaking into chart pieces with local primitives `F_i`,
  and the sum `Σ F_i(t_k) − F_i(t_{k-1})` depends only on the partition
  endpoints — i.e. it equals the PL-in-charts integral. P3 just buries the PL
  logic inside an integration lemma. Resolve it cleanly at the topological level
  instead.
- **P2 is the wrong trade (Q4).** Our continuous-`H₁` (Hurewicz) architecture is
  mathematically stronger and more natural for functoriality than Kirov's
  smooth-only lattice; reversing REFOUND to dodge an elementary lemma discards
  that. Keep our architecture.

### The one implementation fix (Q5) — shrunken-cover, for `IsAnalyticArcStrong`
If `IsAnalyticArcStrong`'s witness needs the segment real-analytic on an OPEN
interval extending slightly past `[t_i, t_{i+1}]`, the extended segment must not
exit the chart. **Fix:** do NOT apply the Lebesgue-number lemma to the maximal
chart domains. Take each chart biholomorphic to an open disk of radius 2 (`D₂`);
let `V_j` be the preimage of the concentric `D₁` (radius 1); apply Lebesgue to
the shrunken cover `{V_j}`. A segment inside `V_j` lies in the strictly convex
`D₁`, and its slight analytic extension stays safely inside `D₂` (a valid chart
domain). This is the standard topological fix and Mathlib handles the metric
pieces (Lebesgue number, convex balls) cleanly.

**Bottom line:** no Whitney, no Grauert, no re-architecture. Prove T-GEN
elementarily via PL on branch `feat/tgen-pl-approx`, using the shrunken-cover
trick for the witness extension; everything downstream is already wired.
