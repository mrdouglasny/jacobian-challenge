# Gap analysis — `exists_cutSurface` (Kirov Dolbeault-port snapshot)

**Target sorry:** `vendor/kirov-jacobian-claude-dolbeault/Jacobians/CutSurfaceRelations.lean:158-161`
(one of the snapshot's 4 sorries, alongside `Abel.lean:671`, `DegreeOneSphere.lean:678`,
`Dolbeault/SerreDualityPairing.lean:127`).

Analysis date: 2026-06-10. All snapshot paths below are relative to
`vendor/kirov-jacobian-claude-dolbeault/`; all "ours" paths relative to repo root.

---

## 1. Exact statement

```lean
theorem exists_cutSurface (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] :
    Nonempty (CutSurface X) := sorry
```
(`CutSurfaceRelations.lean:158-161`.) Here `genus X := Module.finrank ℂ (HolomorphicOneForms X)`
is **analytic** genus (`Genus.lean:66-67`), and `periodVec γ i = lineIntegral (periodBasisForm X i) γ`
(`SmoothPathCore.lean:101-102`).

### `CutSurface X` fields (`CutSurfaceRelations.lean:59-96`)

| Field | Type / content | Nature |
|---|---|---|
| `loop` | `Fin (2 * genus X) → (ℝ → X)` — 2g symplectic-basis loops (line 62) | topological |
| `loop_closed` | `∀ k, IsClosedSmoothLoop (loop k)` (line 64); predicate = closed + continuous + chart-differentiable + velocity-continuous (`SmoothPathCore.lean:109-120`) | regularity |
| `generates` | `closedLoopPeriods X ⊆ Submodule.span ℤ (range (periodVec ∘ loop))` (lines 66-67) — generation **at the period level**, not in H₁ | topology + homotopy invariance of periods |
| `U`, `hbox` | convex open `U ⊆ ℂ` with `wCLM '' ([0,1]×[0,1]) ⊆ U` (lines 70-72) | analytic |
| `h` | `Fin (genus X) → ℂ → ℂ`, pullback coefficients `h_j = cut^*ω_j` (line 74) | analytic |
| `F` | primitives of `h` (line 76) | analytic |
| `hh` | each `h_i` holomorphic **on all of `U` ⊇ the closed box** (line 78) | analytic — see satisfiability flag §4 |
| `hF` | `F_i' = h_i` on `U` (line 80) | analytic |
| `boundaryWord_R1` | `(AᵀB − BᵀA)_{ij} = ∮_{∂box} F_i·h_j dz` with `A,B` = `aPeriodBlock`/`bPeriodBlock` of `loop` (lines 84-86; blocks defined `Dissection.lean:51-58`) | the genuinely topological "boundary word" |
| `boundaryWord_R2` | `(AᵀB̄ − BᵀĀ)_{ij} = − boundaryForm (h j) (F i)` (lines 88-91; `boundaryForm` = `∮_{∂box} F̄·h dz`, `BoundaryPositivity.lean:29-33`) | boundary word, conjugated |
| `nondeg` | nonzero `v` ⇒ `∑ⱼ vⱼ h_j` nonzero somewhere in the **open** box (lines 95-96) | injectivity of pullback |

Note: the structure does **not** contain the cut chart `cut : box → X` itself — only its
analytic shadow (`h`, `F`, the two integral identities, nondegeneracy). Any data satisfying the
identities works; the chart is the natural witness, not a field.

## 2. Consumers in the snapshot — all fully proved conditional on it

Everything downstream is sorry-free given `exists_cutSurface`:

1. **R1 proven**: `CutSurface.cutSurface_R1` (`CutSurfaceRelations.lean:126-130`) via
   `riemann_R1_of_boundaryWord` (`CutSurface.lean:55-63`) = Cauchy on the box
   (`rectBoundaryIntegral_eq_zero_of_differentiableOn`, `CutSurface.lean:43-48`, from Mathlib's
   `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`). **Proved.**
2. **R2 proven**: `CutSurface.cutSurface_R2` (`CutSurfaceRelations.lean:135-137`) via
   `riemann_R2_posDef_of_boundaryWord` (`BoundaryWordR2.lean:131`) + Green-positivity bridge
   `boundaryForm_pos` (`BoundaryPositivity.lean:71-80`, itself from `GreenPositivity.lean` /
   `SurfacePositivity.lean`). **Proved.**
3. `CutSurface.toCanonicalDissection` (`CutSurfaceRelations.lean:141-146`) →
   `exists_canonicalDissection` (`CutSurfaceRelations.lean:167-170`); the `CanonicalDissection`
   structure (`Dissection.lean:83-100`) bundles loops + generation + R1 + R2.
4. `periodVec_linearIndependent` (`Dissection.lean:108-120`, matrix-algebra engine) and
   `realBasis_of_canonicalDissection` (`Dissection.lean:135-159`). **Proved.**
5. `exists_periodLattice_realBasis` (`PeriodLattice.lean:855-860`) — the period lattice is the
   ℤ-span of an ℝ-basis of `ℂ^g`.
6. `instance : DiscreteTopology (truePeriodLattice X)` (`PeriodLattice.lean:865-867`) and
   `instance : IsZLattice ℝ (truePeriodLattice X)` (`PeriodLattice.lean:872-874`) — mechanical
   Mathlib `ZSpan` transports.
7. Downstream of those: the Jacobian as complex torus `ℂ^g ⧸ truePeriodLattice X`
   (root `Jacobians.lean:88-93`; quotient used e.g. `Abel.lean:582`), `ofCurve`, pushforward /
   pullback — the whole challenge API.

So `exists_cutSurface` is the **sole topology/chart input** behind the period-lattice pillar in
Kirov's factoring: both Riemann bilinear relations are theorems over it.

## 3. Bridge to OUR axioms

### Our relevant axioms

* `AX_AnalyticCycleBasis` (`Jacobians/Axioms/AnalyticCycleBasis.lean:265-268`): for every `x₀`,
  `Nonempty (AnalyticCycleBasis X x₀)` where the structure (lines 237-257) demands:
  2g loops as `AnalyticLoop X x₀` (piecewise-real-analytic, refinement-based
  `IsAnalyticArcStrong`, `Jacobians/RiemannSurface/AnalyticArc.lean:73,216-224`), a genuine
  `Module.Basis (Fin (2g)) ℤ (H1 X x₀)`, the Hurewicz tie `loops_to_basis`, and symplectic
  intersection numbers against `intersectionForm`.
* `intersectionForm` axiom-stub + companions `AX_IntersectionForm_alternating`,
  `AX_IntersectionForm_perfect` (`Jacobians/Axioms/IntersectionForm.lean:59-95`).
* Layer-3 Phase-C primitives `AX_RBR1` / `AX_RBR2` (`Jacobians/Layer3/Periods.lean:67-68, 83-85`),
  stated over `periodMap = loopIntegralToH1` (`Jacobians/RiemannSurface/Periods.lean:35-39`,
  `Jacobians/RiemannSurface/LoopIntegral.lean:40`).

### Verdict: a discharged `exists_cutSurface` does NOT directly discharge our topology axioms

The ontologies differ:

| Ours demands | `CutSurface` provides | Gap |
|---|---|---|
| `Module.Basis ℤ (H1 X x₀)` (genuine `Abelianization π₁`) | nothing in H₁ — only period-level generation `closedLoopPeriods ⊆ ℤ-span` (`CutSurfaceRelations.lean:66-67`) | **fundamental**: period-level span ≠ H₁ basis; CutSurface carries no homology at all |
| intersection numbers `⟨α_i, β_j⟩ = δ_{ij}` against the opaque `intersectionForm` | no intersection data of any kind | **fundamental**: our `intersectionForm` is an opaque stub; nothing in CutSurface can be equated to it |
| based loops at a common `x₀`, piecewise-real-analytic (`IsAnalyticArcStrong`) | free loops `ℝ → X`, smooth-ish only (`IsClosedSmoothLoop`) | regularity/basing mismatch (repairable: 4g-gon loops are based and analytic in any honest construction, but the *statement* doesn't say so) |

So: **no, a bridge from the bare statement cannot discharge `AX_AnalyticCycleBasis` or the
`intersectionForm` family.** Any honest *proof* of `exists_cutSurface` (Radó + classification +
4g-gon) would construct exactly the data our axioms assert — but that data is thrown away by the
`Nonempty (CutSurface X)` interface. If we ever co-develop the proof, the right move is to prove a
*strengthened* structure (loops based at `x₀`, `IsAnalyticArcStrong`, H₁-basis + standard
intersection matrix fields) from which both `CutSurface` and `AnalyticCycleBasis` project. This
also matches the recorded `intersectionForm` anchoring debt: "discharge RBR + intersectionForm
jointly" (`AXIOM_AUDIT.md:343`).

### What it WOULD discharge: the analytic content of `AX_RBR1` / `AX_RBR2`

`cutSurface_R1`/`cutSurface_R2` are precisely RBR1/RBR2 **for the cut-surface loops in Kirov's
integration theory**. To convert them into our `AX_RBR1`/`AX_RBR2` (quantified over an arbitrary
`AnalyticCycleBasis b` and our `periodMap`) needs, in order:

1. **Form-space identification**: Kirov `HolomorphicOneForms X` (`ContMDiffSection`,
   `Genus.lean:43-52`) ≅ our `HolomorphicOneForm X`, transporting `genus` (both are
   `finrank ℂ` of the form space — ours `Jacobians/RiemannSurface/Genus.lean:39`, his
   `Genus.lean:66` — so the genus defs align up to the space iso). Mechanical-to-hard Lean.
2. **Integration compatibility**: our `loopIntegralToH1`-value on a class = Kirov `lineIntegral`
   over a representative loop. Our `periodMap` is *defined from the cycle-basis arc integrals*
   (`LoopIntegral.lean:40-60`), so this reduces to comparing two interval-integral pipelines on
   piecewise-analytic loops. Hard-but-standard.
3. **Basis transport**: R1/R2 for *the cut loops* ⇒ R1/R2 for *every* symplectic
   `AnalyticCycleBasis b`. The change-of-basis matrix `M ∈ GL(2g, ℤ)` preserves `Q`-isotropy and
   positivity iff `M ∈ Sp(2g, ℤ)` — which holds iff both bases are symplectic for the **same**
   intersection form. CutSurface has no intersection data, so this step re-imports the
   `intersectionForm` anchoring problem. Alternative: prove RBR1/RBR2 for *one* basis tied to the
   cut loops and re-state our Layer-3 engine over that distinguished basis (the engine in
   `Layer3/Periods.lean` already works from a single basis; `Sp(2g,ℤ)`-transitivity then moves the
   conclusions, per `AXIOM_AUDIT.md:343`). Hard-but-standard given (1)-(2); research-grade if done
   for all bases without intersection anchoring.

Net: the Phase-D bridge value of `exists_cutSurface` is **swapping the research debt of
`AX_RBR1`+`AX_RBR2` (Stokes/Hodge analysis) for the research debt of one topology+chart statement**
— a strictly better factoring (the analysis side is fully machine-checked in the snapshot), but not
an axiom-count reduction on the topology side (`AX_AnalyticCycleBasis`, `intersectionForm` family
remain).

## 4. Decomposition of the missing proof

Classical proof: Radó triangulation → classification of compact oriented surfaces → canonical
4g-gon → uniformization/cut chart → boundary-word computation. Sub-gaps, with available snapshot
infrastructure and ratings:

| # | Sub-gap | What's needed | Snapshot infrastructure | Rating |
|---|---|---|---|---|
| A | **Triangulation + classification** of compact oriented surfaces; canonical 4g-gon model; `H₁ ≅ ℤ^{2g_top}` | Radó (or smooth/Morse route — `X` is real-analytic, so handle decompositions are easier than full Radó); polygon identification space | none — `VanKampen.lean` has only a two-open SVK for *simple connectivity* (built for `S²`, lines 1-50); no homology, no CW, no classification anywhere in Mathlib | **research-grade** (the long pole; a standalone surface-topology project) |
| B | **Analytic genus = topological genus** (`finrank HolomorphicOneForms X = g_top`); baked in because `loop : Fin (2 * genus X)` with `genus` analytic (`Genus.lean:66`) and `nondeg` needs g independent pullbacks | Hodge (`dim H⁰(Ω¹) = ½ b₁`) or Riemann–Roch + `deg K = 2g−2`; depends on finiteness/Serre duality | the snapshot's `Dolbeault/` port (keystone `exists_serreDualityData`; `SerreDualityPairing.lean:127` still sorry) is the intended supplier of finiteness/duality, but the topological-comparison half exists nowhere | **research-grade** (blocked on the Dolbeault/Serre keystone *plus* a de Rham/Hodge comparison) |
| C | **Cut chart with holomorphic margin**: realize `X` minus a cut system as the image of the box interior, with `h_j = cut^*ω_j` holomorphic on a convex open `U ⊇` the **closed** box (`hh`, line 78) | edge interiors: Schwarz-reflection-style extension across the gluing biholomorphism — standard; **corners/vertex preimages: see satisfiability flag below** | none (no uniformization, no fundamental domains) | **research-grade**, and *statement-vet first* |
| D | **Boundary words** (`boundaryWord_R1/R2`): from gluing + primitive-jump data, derive the two `∮_{∂box}` identities | telescoping interval-integral algebra over 4g boundary segments | **single-handle case fully proven**: `rectBoundaryIntegral_singleHandle` (`CutSurface.lean:84-114`) derives `∮ = A·B' − B·A'` purely from gluing/jump hypotheses; the g-handle version is a summed/subdivided variant | **hard-but-standard** (mechanical once C supplies the gluing/jump facts) |
| E | **Generation** (`generates`): every closed-smooth-loop period vector lies in the ℤ-span of the basis periods | (i) π₁-generation by the 2g loops (from A); (ii) **homotopy invariance of `periodVec`** — explicitly acknowledged as missing and only stated in prose (`PeriodLattice.lean:1566-1575`: "Mathlib lacks manifold Stokes") | covering/monodromy toolkit exists (`isCoveringMap_restrictPreimage_compl_branchLocus`, `PeriodLattice.lean:1561-1564`; Mathlib `liftPath_apply_one_eq_of_homotopicRel`); our repo's Fork-1 homotopy-invariance workstream is the natural donor | **hard-but-standard → research-grade** (chart-Cauchy + Lebesgue subdivision, same skeleton as `VanKampen.lean`'s step 1; substantial Lean volume) |
| F | **Nondegeneracy** (`nondeg`): nonzero `v` ⇒ `∑ vⱼ h_j ≠ 0` somewhere in the open box | `∑ vⱼ ωⱼ ≠ 0` (basis) + identity theorem + density of the cut-chart image | identity-theorem machinery exists in snapshot (`MeromorphicLiouville.lean`, isolated-zeros style lemmas elsewhere) | **mechanical / hard-but-standard** given C |

### Satisfiability flag on field `hh` (g ≥ 2) — vet before investing

`hh` demands each `h_j` holomorphic on a *convex open neighborhood of the closed box*. The natural
witness `h_j = cut^*ω_j` requires the cut chart to be conformal **up to and across the boundary**.
Across edge interiors this is fine (the edge identifications are holomorphic deck-type maps;
reflection extends). At the **box corners and at the preimages of the 4g-gon vertices** (all 4g
vertices map to a single point of `X`, total angle 2π split into 4g sectors; the box has 4 corners
of angle π/2 and the remaining 4g−4 vertex preimages sit in edge interiors with angle π), a
conformal chart generically has power-type corner behavior `z^α`, α ∉ ℤ — its derivative (hence
`h_j`) is then **not** holomorphic on any neighborhood of the closed box. For g = 1 the statement
is exactly satisfiable (torus `ℂ/Λ`: `cut` affine entire, `h_j` constant). For g ≥ 2 satisfiability
as stated is **not obvious** and must be vetted (deep-think, one query, per project protocol —
this is the same failure shape as pinned issue #82: a per-cell/per-box strength condition that a
genuine geometric witness may not meet). Possible repairs if vetting fails: require `hh` only on
the open box plus continuity on the closed box (Cauchy and Green both survive: Mathlib's rectangle
theorems need `DifferentiableOn` the closed rectangle minus a countable set / interior versions
exist), or state the boundary integrals over a slightly shrunken box. Since `exists_cutSurface` is
a `sorry`d **theorem** (not an axiom) in the snapshot, an unsatisfiable-for-g≥2 statement costs
wasted effort rather than kernel inconsistency — but if our Phase-D bridge plan maps a research
**axiom** onto it, the satisfiability question becomes load-bearing and must be settled first.

## 5. Alternative routes

### Hyperelliptic-only construction (our concrete family)

The snapshot has **nothing hyperelliptic-specific** (the only mention is prose inside a docstring,
`Abel.lean:690`). Our repo has the full atlas/form stack
(`Jacobians/ProjectiveCurve/Hyperelliptic/` — `Basic`, `Even`/`Odd` atlases, `AffineForm`,
`EvenForm`, `Involution`, …). For `y² = f(x)`:

* **A collapses**: no classification needed — `X` is an explicit double cover of ℙ¹; the 2g
  branch-cut cycles are explicit; H₁/π₁ facts reduce to covering-space arguments over the
  punctured sphere (still nontrivial but standard covering-space Lean, not Radó).
* **B collapses**: the forms `x^k dx/y`, `k < g`, are explicit; `genus = g` is computable
  (our `AX_Hyperelliptic_genus` track, `docs/planning/AX_Hyperelliptic_genus.md`).
* **E gets cheaper**: monodromy over ℙ¹ minus branch points; the snapshot's covering toolkit
  (`PeriodLattice.lean:1556-1564`, `LoopOffBranch.lean`) is directly usable.
* **C/D do NOT collapse**: the single-box cut chart with holomorphic margin is no easier on the
  two-sheet model than in general (the corner issue of §4 is identical); the boundary-word
  integrals would still have to be routed through some explicit slit-plane parametrization.

So the hyperelliptic shortcut roughly halves the problem (kills A, B, most of E) but leaves the
hardest analytic sub-gap C intact. Also note: `exists_cutSurface` quantifies over **all** compact
connected Riemann surfaces — a hyperelliptic-only construction discharges a *restricted* variant,
useful for our concrete-family pipeline, not for closing the snapshot's sorry.

### Genuinely cheap case: g = 1

`ℂ/Λ` (and our elliptic witnesses, `Jacobians/ProjectiveCurve/Elliptic/Witnesses.lean`, the
`ComplexTorus` cycle machinery): `cut z = π(z₁ + x·ω₁ + y·ω₂)` is entire, `h = const`, both
boundary words are two-line computations of the single-handle identity
(`rectBoundaryIntegral_singleHandle` applies verbatim), `nondeg` is trivial. Rating:
**hard-but-standard, small**. Worth doing as the satisfiability witness for the structure and as a
dry run of D/F — but it does not discharge the universally-quantified theorem.

## 6. Recommended attack order

1. **Vet first (cheap, blocking).** One deep-think query: is `CutSurface.hh` (holomorphy on a
   convex open ⊇ closed box) satisfiable for g ≥ 2 by any genuine cut chart, or must it be
   weakened to interior-holomorphy + boundary continuity? (§4 flag.) Do this *before* any
   Phase-D bridge maps a research axiom onto `exists_cutSurface`.
2. **g = 1 witness** on `ℂ/Λ` via `rectBoundaryIntegral_singleHandle` — validates the structure,
   exercises D and F, reuses our elliptic cycle witnesses. Days, not weeks.
3. **Bridge the analytic engine, not the topology.** Port Kirov's proven chain
   (`riemann_R1_of_boundaryWord`, `riemann_R2_posDef_of_boundaryWord`, `boundaryForm_pos`,
   Dissection engine) and aim our `AX_RBR1`/`AX_RBR2` discharge plan at a *strengthened*
   CutSurface (based, analytic loops + H₁-basis + intersection fields) so that one future
   construction discharges `AX_RBR1`, `AX_RBR2`, `AX_AnalyticCycleBasis`, and anchors
   `intersectionForm` simultaneously (per the joint-discharge note, `AXIOM_AUDIT.md:343`).
   Until then, do **not** trade our vetted RBR primitives for `exists_cutSurface` — equal research
   debt, worse alignment with our H₁ layer.
4. **Hyperelliptic restricted variant** (optional, concrete-family leverage): explicit cycles +
   forms + covering monodromy give a CutSurface-for-hyperelliptic modulo sub-gap C; pursue only if
   step 1 lands a satisfiable (possibly weakened) `hh`.
5. **Long pole, separate projects**: A (surface classification / 4g-gon — a standalone topology
   formalization) and B (analytic = topological genus — blocked on the Dolbeault/Serre keystone
   `exists_serreDualityData` + a Hodge/de Rham comparison). Neither should be scheduled inside
   this repo's critical path now.


---

## §4 flag RESOLVED (2026-06-10, deep-think): satisfiable as stated; geometric witness impossible for g ≥ 2

The satisfiability suspicion is settled with a split verdict:

- **The structure as stated is SATISFIABLE for all g ≥ 0** — it carries no cut
  chart, only abstract `h, F : ℂ → ℂ` plus the two boundary-word ∮ identities.
  Abstract witness: genuine symplectic loops (R1/R2 classically true) + g
  polynomials Gram-matched (Cholesky) to `G = ½·i(AᵀB̄ − BᵀĀ) ≻ 0`; the Green
  constant and boundary words check out. g = 1: constant `h` with `|c|² = Im τ`
  (NB the earlier "affine entire chart" claim above is wrong for generic τ —
  the chart is only ℝ-linear — but irrelevant to the witness). So mapping our
  axioms onto `exists_cutSurface` is kernel-safe.
- **But the corner suspicion is CONFIRMED for the intended geometric route**:
  the angle count `4·(π/2) + (4g−4)·π = (4g−2)π > 2π` rigorously rules out a
  holomorphic-on-closed-box cut chart for g ≥ 2.
- **Strategic consequence:** the only non-circular witnesses at g ≥ 2 are
  abstract (they presuppose R1/R2 proven by other means), so the structure's
  value as a *proof factoring* is weaker than its docstring suggests. An honest
  discharge of the sorry must either weaken `hh` to interior-holomorphy +
  boundary continuity (re-enabling the Riemann-map witness; Mathlib's rectangle
  theorems tolerate this) or prove R1/R2 independently first.
