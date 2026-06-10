# AX_AnalyticCycleBasis (#16) — alternatives scout

Date: 2026-06-10. Baseline being challenged: the π₁-presentation 4g-gon route
(#16 plan comment 2026-06-10), est. **2–4 months** for (i)–(iv), with the
analytic-genus = topological-genus gate (v) as a hard blocker on top (Gemini
verdict, caveat (3)). This document audits five alternative directions with
file:line evidence and ends with a recommended combination and the owner's
decision points.

**Scope note.** Buzzard's headlines quantify over arbitrary compact connected
`X`, so nothing family-specific can *close* #16; family work is de-risking and
Part-3 witness value only. The challenge-critical count is 10 after the trace
discharges (`docs/CHALLENGE_AXIOM_CLOSURE.md` Cluster-C status note); the
#16-coupled block inside it is **4 axioms**: `AX_AnalyticCycleBasis`,
`intersectionForm`, `AX_RBR1`, `AX_RBR2`.

---

## 0. Ground truth: what consumers actually use

Structure fields (`Jacobians/Axioms/AnalyticCycleBasis.lean:237-257`) vs.
actual consumption:

| Field | Consumers (file:line) | Verdict |
|---|---|---|
| `loops` | `RiemannSurface/LoopIntegral.lean:22,47` (integrability + arc period functionals), `LoopIntegralHom.lean:126-128`, `ProjectiveCurve/Elliptic/OfCurveInj.lean:198-226` | **needed** — supplies the integrable representatives |
| `isBasis` | `LoopIntegral.lean:45` (`cb.isBasis.constr ℤ` — *defines* `loopIntegralToH1`, i.e. the period map, sidestepping homotopy invariance), `Layer3/Periods.lean:36-43,106-112` (`periodVec` via `αEmbed`/`βEmbed`), `:432` (`range_eq_span_image` — spanning gives lattice = ℤ-span of 2g columns), `Axioms/H1FreeRank2g.lean:46`, `OfCurveInj.lean:195-233` (`sum_repr`), `Line/Witnesses.lean:51` | **needed** — both freeness (for `constr`) and the `Fin (2·g)` indexing (for the square-matrix engine) are load-bearing |
| `loops_to_basis` | `LoopIntegral.lean:63` (`loopIntegralToH1_loop`), `LoopIntegralHom.lean:127`, `OfCurveInj.lean:202` | **needed**, but **costless**: `H1 := Additive (Abelianization (FundamentalGroup X x₀))` (`RiemannSurface/Homology.lean:41-42`), so the "Hurewicz tie" is just "basis vector := class of the loop". Don't drop it. |
| `symplectic` | **ZERO consumers.** `grep -rn '\.symplectic'` over `Jacobians/` (excl. Vendor): no hits outside the structure definition. | type-level only — but it drags `Axioms.intersectionForm` into **every** Buzzard declaration (`docs/axiom-report.txt:5-77`) |

**The hidden role of `symplectic`.** Although no proof destructures it, it is
the *satisfiability guard* for `AX_RBR1`/`AX_RBR2`
(`Layer3/Periods.lean:67-68,83-85`), which quantify over **every**
`b : AnalyticCycleBasis X x₀`. Dropping the field naively makes RBR1/RBR2
**false**: a `GL(2g,ℤ) ∖ Sp(2g,ℤ)` re-indexing of a genuine basis (e.g. swap
one α/β pair, g = 1: negates `Q`) still inhabits the weakened structure but
violates isotropy/positivity. So any weakening must be co-designed with the
RBR statements. This is DT's "global-choice trap" in another guise.

**Second hidden cost of `symplectic`.** Because `intersectionForm` is an
*opaque axiom carrier* (`Axioms/IntersectionForm.lean:59`), the `symplectic`
field is **unprovable for any concrete witness** — no proof can compute values
of an opaque form. That is exactly why the elliptic witness is axiom-wrapped
(`AX_Elliptic_H1_symplectic`, `ProjectiveCurve/Elliptic/Witnesses.lean:495-503`):
the loops, basis, and `loops_to_basis` are constructible there, the symplectic
field is not, *by design of the current structure*. The field actively blocks
the entire concrete-witness de-risking program (elliptic now, hyperelliptic
later) until `intersectionForm` is defined (#22).

---

## 1. Consumer-weakening — restate the axiom as a bundled "dissection datum"

**Proposal.** Merge `AX_AnalyticCycleBasis + AX_RBR1 + AX_RBR2` into ONE axiom
over a weakened structure, and state R1/R2 **arc-level** (over the bundled
loops' own `canonicalArcIntegral`s, not over the global `periodMap`):

```
structure PeriodCycleBasis (X) (x₀) where
  loops          : Fin (2 * genus X) → AnalyticLoop X x₀
  isBasis        : Module.Basis (Fin (2 * genus X)) ℤ (H1 X x₀)
  loops_to_basis : ∀ i, isBasis i = loopToHomology (loops i)
  R1 : ∀ η ζ, Q (arcPeriodVec loops η) (arcPeriodVec loops ζ) = 0
  R2 : ∀ η ≠ 0, 0 < (I * Q (arcPeriodVec loops η) (conjArcPeriodVec loops η)).re

axiom AX_PeriodCycleBasis (x₀ : X) : Nonempty (PeriodCycleBasis X x₀)
```

where `arcPeriodVec` is `periodVec` with `periodMap X x₀ (b.isBasis _)`
replaced by `arcPeriodFunctional (loops _).arc` — the two agree on the chosen
witness by `loopIntegralToH1_loop` (`LoopIntegral.lean:52-64`). No
`intersectionForm`, no `symplectic` field.

**Honesty check (vetting rules).** The merged statement is verbatim "every
compact Riemann surface has a canonical homology basis satisfying Riemann's
bilinear relations" — Griffiths–Harris Ch. 2 §2, Forster §§20–21. It is
**strictly implied by the current axiom set** (instantiate RBR1/RBR2 at the
chosen basis), so satisfiability is inherited from the 2026-06-09 DT vettings
of all three. Weaker-or-equal, never stronger — the safe direction under the
project's strengthening rule. It is also exactly the shape Kirov factored
independently: `CanonicalDissection`
(`vendor/kirov-dolbeault-port/KirovDolbeault/Dissection.lean:83-100` = loops +
generation + R1 + R2, arc-level via `aPeriodBlock`/`bPeriodBlock`,
`Dissection.lean:51-58`). Two independent designs converging on the same
interface is good evidence it is the right primitive.

**What changes downstream (audited):**

- `loopIntegralToH1` (`LoopIntegral.lean:40-48`): identical modulo structure
  name — uses only `loops`/`isBasis`/`loops_to_basis`.
- Layer-3 engine (`Layer3/Periods.lean`): mechanical refactor. The engine
  lemmas (`tauMatrix_isSymm:219`, `tauMatrix_posDef:274`, …) take `hR1`/`hR2`
  as hypotheses instead of invoking axioms; `riemannBilinear_exists:339-357`,
  `periodLatticeInBasis_discrete:501-510`, `periodLatticeInBasis_isZLattice:515-530`
  run on the **chosen** witness (the one technical subtlety: the engine must
  use the same `Classical.choice` witness that defines `loopIntegralToH1`, in
  the existing `loopIntegralToH1_loop` pattern; bundling R1/R2 with the data
  is precisely what makes this sound and dissolves DT's global-choice trap).
- `AX_RiemannBilinear` (now a theorem, `Axioms/RiemannBilinear.lean:72-83`):
  statement survives — consumes `b.isBasis` only.
- Lattice discreteness / `instPeriodLatticeDiscrete`, Period-Triangle
  `ofCurve_inj` (`OfCurveInj.lean`), `H1FreeRank2g`: **nothing breaks** —
  verified field-by-field above.
- `intersectionForm` drops out of every Buzzard `#print axioms`
  (it enters only via the `symplectic` field type). The two law axioms
  (already zero-consumer, closure doc §i) become fully orphaned.
- `AX_Elliptic_H1_symplectic` (`Witnesses.lean:495`) becomes **dischargeable**:
  at g = 1 the form space is 1-dimensional so R1 is trivial
  (`Q(P(η),P(ζ)) = 0` for proportional forms), and R2 is `Im(ω₂/ω₁) > 0` —
  the elliptic hypothesis. The existing A/B-loop constructions
  (`Witnesses.lean:470-490` + the d4f6e82 strong-arc work) complete the witness.

**Axiom-count effect.** Challenge-critical 10 → **7** (4 merge into 1).
Ledger: −2 orphaned intersection laws, −1 `AX_Elliptic_H1_symplectic`
(discharged), −1 `AX_H1FreeRank2g` consumer unchanged. `intersectionForm`
itself: owner's choice (see D2).

**What it does NOT change.** The irreducible mathematical content — 2g
analytic loops whose classes freely generate `H1` with rank exactly
`2 · genus_analytic`, satisfying R1/R2 — is untouched, and the
genus-comparison gate stays baked into `Fin (2 * genus X)`. This direction
buys *count, alignment, witness-unblocking, and trap-removal*, not a cheaper
discharge of the core.

**Rating: HIGH viability.** Cost: **~1–2 weeks agent time** (axiom file,
Layer-3 refactor, witnesses, AXIOM_AUDIT/README/axiom-report in same commits).
Major-change protocol: needs a GitHub Discussion before the PR (CLAUDE.md).

### Why not weaken further (to period-level generation, no H1 basis)?

`CutSurface.generates` is period-level ℤ-generation *without* H₁
(`CUTSURFACE_GAP_ANALYSIS.md` §3). Adopting that as the axiom would break
`loopIntegralToH1`: `Basis.constr` needs a free-module basis — that is the
device that *defines* the period map on `H1` without homotopy invariance
(`LoopIntegral.lean:44-48`). Replacing it means defining the lattice as a bare
ℤ-span (Kirov's `truePeriodLattice`) and re-deriving the Jacobian, i.e.
Direction 5. Also `generates` smuggles in homotopy invariance of periods
(sub-gap E, research-grade, the X1 workstream). Keep the H1 basis.

---

## 2. Branched-cover / monodromy route

**Which X are actually in scope?** For *closing* #16: all compact connected
Riemann surfaces (Buzzard quantifies over arbitrary `X`). Concrete Part-3
families: `ProjectiveLine` (witness already axiom-free,
`Line/Witnesses.lean:90-101`, genus 0), `Elliptic` (witness axiom-gated — see
§1), `HyperellipticOdd/Even`, `PlaneCurve`.

**Available machinery (axiom-free, compiled in our build via the Lake path
dep `vendor/kirov-dolbeault-port`, `lakefile.toml:28`):**

- `MeromorphicFunction.toRiemannSphere` — *any* meromorphic function is a
  holomorphic map `X → ℂℙ¹` (`KirovDolbeault/ToSphereGeneral.lean:60-67`,
  proven).
- Proper-map degree / sheet machinery (`ProperMapDegree*.lean`), covering off
  the branch locus (`isCoveringMap_restrictPreimage_compl_branchLocus`,
  `PeriodLattice.lean:1561-1564`), chart-local FTC + detour surgery
  foundations (`LoopOffBranch.lean:6-40`).
- Wallace `BranchedCover.lean` (`Jacobians/Vendor/Wallace/HolomorphicForms/`,
  sorry/axiom-free): branched-cover data, `branchedDegree`, fiber-sum
  constancy.

**(a) Hyperelliptic-only.** The degree-2 map is the x-projection — *not yet
formalized as a map to ℙ¹* in `Jacobians/ProjectiveCurve/Hyperelliptic/` (no
sphere-map decl; only atlases/forms/involution). The classical aᵢ/bᵢ loops
around branch-point pairs are fully explicit. Proof skeleton: double cover of
ℙ¹ minus 2g+2 branch points; loops around branch pairs lift to closed loops;
π₁/H1 facts via covering-space theory (Mathlib has covering lifting +
Nielsen–Schreier; missing: π₁ of a punctured sphere is free — needs an
SVK-style argument, buildable on the Lebesgue-subdivision + telescoping
skeleton of Kirov's proven `VanKampen.lean`). Yields a `PeriodCycleBasis`
witness for the family, synergizes with `AX_Hyperelliptic_genus`, and the R1/R2
fields can be inherited from explicit branch-cut period computations or the
boundary-word engine. **Rating: hard-but-standard, est. 4–8 weeks**, contingent
on §1 landing first (otherwise the witness is unfinishable, as with elliptic).
Does **not** close #16.

**(b) General X.** Post-keystone (`exists_serreDualityData` → RR), a
nonconstant meromorphic function exists, so `toRiemannSphere` gives every `X`
a finite branched cover of ℙ¹ **for free**. This enables the classical
*slit-sheet* proof of the cycle basis: cut ℙ¹ along arcs joining branch
points, the sheets glue into an explicit polygon — i.e. **the branched cover
replaces both Radó triangulation and abstract surface classification**, the
two items the baseline plan rates as the long pole (#16 plan deliverable (i)).
The remaining topological work — monodromy bookkeeping, π₁ of punctured
sphere (SVK-lite), Nielsen–Schreier (in Mathlib), filling punctures, rank via
Riemann–Hurwitz — is substantial but incremental, with concrete analytic
objects throughout instead of abstract 2-manifolds. The genus-comparison gate
is *partially* internalized: RR computes `dim H⁰(Ω¹)` on the same analytic
side that defines `genus`, and Riemann–Hurwitz gives the Euler characteristic
of the cover combinatorially; one still must connect "rank of the constructed
H1 basis" to `2 · genus_analytic`, so the gate does not vanish, but it is
attacked with RR tools that the keystone supplies rather than with a separate
Hodge/de Rham comparison. **Rating: research-grade, est. 2–4 months *after*
the keystone**, replacing baseline items (i)+(ii) with cheaper analytic
analogues. This is the recommended general-X route.

---

## 3. The port's assets against a weakened statement

| Asset | Status | Fit |
|---|---|---|
| `CanonicalDissection` + matrix engine: `periodVec_linearIndependent` (`Dissection.lean:108-120`), `realBasis_of_canonicalDissection` (`:135-159`) | proven | the *interface twin* of the §1 merged axiom; R2 ⇒ ℝ-independence ⇒ full lattice, no H1 needed at this layer |
| `exists_periodLattice_realBasis` (`PeriodLattice.lean:855-860`) + discreteness/`IsZLattice` instances (`:865-874`) | proven *conditional on* `exists_cutSurface` (sorry, `CutSurfaceRelations.lean:158-161`) | parallel to our own discharged lattice chain; no new content for us |
| R1/R2 from boundary words: `riemann_R1_of_boundaryWord` (`CutSurface.lean:55-63`), `riemann_R2_posDef_of_boundaryWord` (`BoundaryWordR2.lean:131`), `boundaryForm_pos` (`BoundaryPositivity.lean:71-80`) | proven | **the discharge path for the R1/R2 fields** of the merged axiom, once any polygon/cut construction exists; single-handle boundary word fully proven (`rectBoundaryIntegral_singleHandle`, `CutSurface.lean:84-114`) |
| `VanKampen.lean` two-open SVK (simple-connectivity version) | proven | not a π₁-presentation SVK, but the Lebesgue-subdivision + spokes + telescoping method is exactly what both the full SVK and the monodromy generation arguments need — method de-risked |
| `SmoothPath`/`LoopOffBranch` chart-local FTC | proven | feeds X1 (homotopy invariance) and route 2's monodromy lifting |

**On the C1 finding** ("CutSurface carries period-level ℤ-generation without
H₁ — exactly matching a consumer-weakened axiom?"): only if the weakening
also abandons the H1 basis, which §1 shows breaks `loopIntegralToH1`'s
definition. The correct division of labor: the port inhabits the **R1/R2 and
lattice-engine half** of the weakened axiom; the **H1 half** (loops + free
basis) stays ours. The CUTSURFACE doc's §6 step-3 recommendation (one
*strengthened* construction projecting onto both interfaces) is unchanged —
and the §1 merged axiom is exactly that projection target on our side.

---

## 4. Radó / triangulation-lite

- Full Radó is **unnecessary for this project**: every route that needs a
  polygon model can get it from the branched cover (Direction 2b), because
  analyticity supplies the cover that abstract topology would need
  triangulation for. Formalizing Radó + classification as a standalone
  project (baseline (i)) is the *most expensive* way to obtain the polygon.
- Morse theory on a harmonic function: previously rejected — "formalization
  trap … fatal flaw regarding real-analyticity at critical point closures"
  (`docs/planning/AX_AnalyticCycleBasis.md:31`, Gemini critique `:82`). Do not
  reopen.
- "Just 2g loops generating H1" without classification: generation without
  freeness doesn't feed `Basis.constr`, and the rank-2g pin *is* the genus
  comparison; no cheap topological shortcut exists. g = 0 is done
  (`Line/Witnesses.lean`); g = 1 is covering theory (active de-risk, becomes
  fully closable after §1).
- **Honest rating: research-grade with no discount**; pursue only as a
  by-product of Direction 2b. The genus-comparison gate (Gemini caveat (3))
  binds every route equally — it is a property of the axiom's `Fin (2*genus X)`
  type, not of the proof strategy.

---

## 5. Construction swap (avoid H1 altogether)

The expensive properties, pinned per consumer:

| Property | Needed by | Genuinely expensive? |
|---|---|---|
| **freeness + finite rank 2g** of `H1` | `Basis.constr` defining `loopIntegralToH1` (`LoopIntegral.lean:45`); square-matrix engine (`Layer3/Periods.lean:103-200`) | **YES — this is the core cost**, inseparable from the genus comparison |
| **symplectic / intersection data** | no proof, anywhere (§0) | NO — pure satisfiability scaffolding for RBR; eliminated by §1 |
| **analytic representatives** | integrability (`AX_cycleBasisLoop_integrable`, now a theorem over `IsAnalyticArcStrong`, `LoopIntegral.lean:17-23`) | NO — hard-but-standard approximation, and only needed for the 2g chosen loops |

A Kirov-style period-level Albanese (`Jacobian := ℂ^g ⧸ ℤ-span of 2g period
vectors`, no H1) would trade freeness for `generates` — which imports homotopy
invariance of periods (research-grade, currently quarantined inside
`exists_cutSurface` sub-gap E) — and would force redefining
`Jacobian`/`JacobianAmbient` (`Jacobian/Construction.lean:130-149`), `ofCurve`,
and re-validating all 24 Buzzard obligations + `ChallengeConformance`.
"H1 := π₁^ab is already the def" cuts the other way: the current model gets
well-definedness of periods *by definition* on the basis, deferring homotopy
invariance to the recorded X1 faithfulness debt (closure doc, boundary 4),
which the swap would instead place on the critical path immediately.
**Rating: REJECT** — months of churn, higher regression risk, no reduction of
the genuinely expensive property.

---

## Recommendation (combination)

1. **Now (1–2 wk): land Direction 1** — merge `AX_AnalyticCycleBasis` +
   `AX_RBR1` + `AX_RBR2` into one arc-level `PeriodCycleBasis` axiom; drop the
   `symplectic` field and the `intersectionForm` type-dependency.
   Challenge-critical 10 → 7; trap dissolved; concrete witnesses unblocked.
   Open a GitHub Discussion first (major change / shared interface).
2. **Days after: g = 1 witness** — discharge the elliptic witness (deletes
   `AX_Elliptic_H1_symplectic`), validating the schema end-to-end at the only
   genus where the loops already exist in-repo.
3. **Parallel (4–8 wk): hyperelliptic branch-cut basis** (Direction 2a) —
   formalize the x-projection to ℙ¹ over the port's covering toolkit; Part-3
   witnesses + `AX_Hyperelliptic_genus` synergy.
4. **General discharge (post-keystone, 2–4 mo): Direction 2b** — branched
   cover from an RR-supplied meromorphic function; slit-sheet polygon replaces
   Radó + classification; R1/R2 fields discharged through the port's proven
   boundary-word engine (Direction 3). Do **not** start the standalone
   classification project (baseline (i)) — it is dominated by 2b on every
   axis once the keystone lands, and the keystone is already the project's
   committed Phase-D track.

**Net vs. baseline:** the 2–4-month figure does not disappear — it moves
post-keystone and is attacked with analytic tools that exist instead of
topology that doesn't, while the next 2–6 weeks yield concrete count
reductions (10 → 7 critical, plus 3 ledger axioms) that the baseline route
would only deliver at the very end.

## Decision points for the owner

- **D1.** Approve the merged restatement (Discussion thread)? It removes the
  symplectic/intersection content from the challenge cone, retaining it only
  as documentation/Part-3 debt. (Recommended: yes — the content was never
  consumed by a proof and blocks all witnesses.)
- **D2.** Fate of `intersectionForm` + 2 laws + #22: (a) delete from the build
  (cleanest ledger), or (b) keep and later *define* the form as the coordinate
  symplectic form of the chosen basis (the existing #16+#22 joint plan) for
  topological-anchoring value. Orthogonal to D1; can be deferred.
- **D3.** Sequencing constraint: elliptic/hyperelliptic witnesses are
  *unprovable before* D1 lands (opaque-form obstruction, §0). If D1 is
  rejected, the witness program needs #22's `intersectionForm` definition
  first — strictly more work in a worse order.
- **D4.** General-X route selection — defer until the Serre keystone lands;
  decide then between 2b (recommended) and the 4g-gon classification project.
  No classification work should be scheduled now either way.
- **D5.** Unchanged debts to keep visible: X1 homotopy invariance (faithfulness
  of the H1 period model; required for `AX_ofCurve_contMDiff`'s truth) and the
  genus-comparison gate — neither is created nor removed by any direction
  here, and the gate binds the eventual discharge of the merged axiom exactly
  as it bound the original.
