# T-GEN final reduction — the last challenge axiom reduces to {Whitney, Grauert}

**Headline.** The entire Buzzard-challenge endgame's last topological axiom,
`AX_PeriodCycleBasis`, reduces — *fully formalized, sorry-free, no new axiom* —
to **two classical real-analytic approximation theorems that Mathlib lacks**:

1. **Whitney** (continuous ⇝ smooth loop, rel endpoints), and
2. **Grauert / Whitney–Bruhat** (smooth ⇝ real-analytic loop, rel endpoints).

This document records the complete proven reduction chain, the composition
theorem that ties it together, the exact statements of the two
walls, why each is Mathlib-absent, and the hyperelliptic alternative.

> **Important correction (2026-06-13, after studying Kirov's submission).**
> Whitney and Grauert are walls *only for the **constructive** route taken here*
> — the route that insists on **exhibiting an explicit integral homology basis**
> (analytic loops generate H₁ ⟹ smooth/analytic loop approximation). They are
> **not intrinsic to the challenge.** Kirov's submission (`../jacobian-claude`)
> proves Buzzard's 24 sorry-free **and axiom-free** by a **non-constructive**
> route that never exhibits cycles: it spans *all* closed loops, proves (a)
> lattice **discreteness** (isolated-zero/residue — what our K-LITE already
> proves) and (b) **period-pairing non-degeneracy**
> (`span_real_truePeriodLattice_eq_top`, a maximum-principle argument), and lets
> Mathlib's `ZLattice` theory produce a rank-2g basis *by existence*. No T-GEN,
> no Whitney, no Grauert, no R1/R2. The genuine remaining content for **us** is
> therefore **not** these approximation theorems but the single non-degeneracy
> lemma — see [`NONCONSTRUCTIVE_DISCHARGE_PLAN.md`](NONCONSTRUCTIVE_DISCHARGE_PLAN.md).
> The reductions below remain valid Lean; they are just no longer the shortest
> path to closing the axiom.

Companion: `TGEN_ROUTE.md` (the route map + gap ledger), Discussion #235
(K-FULL endgame).

The composition lives in
`Jacobians/RiemannSurface/TGenFinalReduction.lean`.

---

## 1. The complete proven reduction chain

Reading **top-down** (the axiom we want) to **bottom** (the two named walls).
Every link marked **PROVEN** is sorry-free and `#print axioms`-clean
(`[propext, Classical.choice, Quot.sound]` only — no `sorryAx`, no project
axiom, in particular **not** `AX_PeriodCycleBasis` itself).

```
AX_PeriodCycleBasis                         (the challenge's last axiom)
   ▲  PeriodCycleBasis.lean:237
   │  needs: a piecewise-analytic ℤ-basis of H₁ satisfying Riemann bilinear
   │  relations.  T-GEN supplies the spanning half (basis ⇐ spanning + period
   │  injectivity, exists_h1LoopBasis_of_periodInjective).
   │
   │  PROVEN  H1Composite.lean:289  exists_h1LoopBasis_of_periodInjective
   │  PROVEN  H1Composite.lean:332  analyticLoopsGenerateH1_of_h1LoopBasis
   ▲
AnalyticLoopsGenerateH1 x₀   ( = T-GEN )    H1Composite.lean:105
   ▲
   │  PROVEN  AnalyticPi1Generation.lean:113  analyticLoopsGenerateH1_of_pi1_closure
   │          (the K0 keystone bridge: (P) ⟹ T-GEN, abelianization algebra)
   ▲
pi1AnalyticClasses x₀ = ⊤   ( = property (P) )
   ▲
   │  PROVEN  AnalyticApproxGeneration.lean:118  analyticLoopsGenerateH1_of_analyticRep
   │          (AAW ⟹ (P) ⟹ T-GEN, via loopToPi1 surjective)
   ▲
ContinuousLoopHasAnalyticRep x₀   ( = AAW )   AnalyticApproxGeneration.lean:75
   ▲
   │  ┌──────────────────  THE COMPOSITION (this file)  ──────────────────┐
   │  │  PROVEN  TGenFinalReduction.lean                                   │
   │  │  analyticLoopsGenerateH1_of_smoothApprox_analyticApprox            │
   │  │                                                                    │
   │  │  continuous loop p                                                 │
   │  │     │  SmoothLoopApproxHyp (Whitney)        [WALL 1]               │
   │  │     ▼                                                              │
   │  │  smooth path δ,  IsSmoothPath 𝓘(ℂ) δ                              │
   │  │     │  RECONCILE: IsSmoothPath 𝓘(ℂ) δ  ≡  IsSmoothCurve δ.extend   │
   │  │     ▼            (definitional, Iff.rfl — no gap)                  │
   │  │  smooth curve δ.extend,  IsSmoothCurve δ.extend                    │
   │  │     │  SmoothLoopAnalyticApprox (Grauert)    [WALL 2]              │
   │  │     ▼                                                              │
   │  │  AnalyticLoop δₐ,  loopToPath δₐ ≃ curveToPath δ.extend = δ        │
   │  │     │  Path.Homotopic.trans  with  δ ≃ p                           │
   │  │     ▼                                                              │
   │  │  loopToPath δₐ ≃ p     ⟹  ContinuousLoopHasAnalyticRep x₀ (AAW)   │
   │  └────────────────────────────────────────────────────────────────┘
   ▲
   │  two named classical hypotheses (explicit arguments):
   │
SmoothLoopApproxHyp X            SmoothLoopApprox.lean:120     [WALL 1 — Whitney]
∀ y, SmoothLoopAnalyticApprox y  SmoothAnalyticLoop.lean:175   [WALL 2 — Grauert]
```

### The composition theorem (exact statement)

```lean
theorem analyticLoopsGenerateH1_of_smoothApprox_analyticApprox {x₀ : X}
    (hsmooth : SmoothLoopApproxHyp (H := ℂ) (IM := 𝓘(ℂ)) X)
    (hanalytic : ∀ y : X, SmoothLoopAnalyticApprox y) :
    AnalyticLoopsGenerateH1 x₀
```

with
`variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]`.

`#print axioms analyticLoopsGenerateH1_of_smoothApprox_analyticApprox`
=
`[propext, Classical.choice, Quot.sound]`.
No `sorryAx`, no new axiom; the two walls appear **only** as explicit
hypotheses `hsmooth`, `hanalytic`.

### The reconciliation was CLEAN (no third wall)

The mission flagged the `IsSmoothPath ↔ IsSmoothCurve` junction as the place a
hidden gap could hide (different parametrisation domain, smoothness order, or
endpoint handling). It is **clean**:

* `IsSmoothPath 𝓘(ℂ) δ`
  `:= ∀ r, ContDiffAt ℝ ∞ (fun u => extChartAt 𝓘(ℂ) (δ.extend r) (δ.extend u)) r`
  (`SmoothLoopApprox.lean:80`), and
* `IsSmoothCurve (δ.extend)`
  `:= ∀ r, ContDiffAt ℝ ∞ (fun u => extChartAt 𝓘(ℂ) (δ.extend r) (δ.extend u)) r`
  (`SmoothAnalyticLoop.lean:96`)

are **definitionally identical**: same moving-chart readout `extChartAt 𝓘(ℂ)`,
same domain `ℝ` (`δ.extend : ℝ → X`, *both* lanes already live on all of `ℝ`,
not `[0,1]`), same order `∞ : ℕ∞ω`, same pointwise quantifier. The
reconciliation lemma is literally `Iff.rfl`:

```lean
theorem isSmoothPath_iff_isSmoothCurve_extend {x₀ : X} (δ : Path x₀ x₀) :
    IsSmoothPath 𝓘(ℂ) δ ↔ IsSmoothCurve δ.extend := Iff.rfl
```

The two lanes were authored against the **same moving-chart smoothness
convention** precisely so this junction would be free — both deliberately use
`extChartAt 𝓘(ℂ)`-readout `ContDiffAt ℝ` to sidestep the real-vs-complex
`ModelWithCorners` scalar diamond a naive `ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℂ)` predicate
would create. The *only* non-`rfl` bookkeeping is that the path of the curve
`δ.extend` is `δ` itself (`curveToPath_extend_eq`, by `Path.extend_extends'`),
which lets the two homotopies compose by `Path.Homotopic.trans`.

**No third hypothesis was needed.** There is no order mismatch (both `C^∞`), no
`[0,1]`-vs-`ℝ` mismatch (both predicates are stated on `ℝ` and applied to
`δ.extend`), and the endpoints are handled by `Path.extend_zero` /
`Path.extend_one`.

---

## 2. The two irreducible walls (exact statements + why Mathlib-absent)

### WALL 1 — `SmoothLoopApproxHyp` (Whitney smooth approximation, manifold target)

`Jacobians/RiemannSurface/SmoothLoopApprox.lean:120`:

```lean
def SmoothLoopApproxHyp (X : Type*) [TopologicalSpace X] [ChartedSpace H X]
    [IsManifold IM 0 X] : Prop :=
  ∀ {x₀ : X} (γ : Path x₀ x₀),
    ∃ δ : Path x₀ x₀, IsSmoothPath IM δ ∧ γ.Homotopic δ
```

*Every continuous loop is homotopic rel endpoints to a smooth one.*

**Why Mathlib-absent.** Mathlib (mid-2026) has
`Continuous.exists_contMDiff_approx_and_eqOn`: uniform `C^n` approximation of a
continuous map **into a normed space**, with `EqOn` on a closed set — but **no
manifold-codomain version** and **no homotopy conclusion**. Bridging to a
manifold target requires covering `[0,1]` by finitely many chart cells, pulling
back to the model `ℂ` (a normed space), approximating there, pushing forward,
and gluing; the cross-cell glue is `C⁰` but generically has corners, so it is
not globally `ContMDiff`. The standard remedy (reparametrize locally constant at
junctions, approximate rel a neighborhood of the junctions) is a multi-file
differential-calculus build-out, not a Mathlib lemma. The unconditional gluing
engine (`Path.homotopic_of_chain`, `SmoothLoopApprox.lean:88`, and the
chart-local straight-line homotopy `Path.homotopic_of_extChartLocal`,
`ChartLocalHomotopy.lean:127`) is already proven here; the residual is exactly
the junction-bookkeeping core.

**Effort estimate: ~3–5 active days** (one differential-topology build-out; the
topological packaging is already in this lane).

### WALL 2 — `SmoothLoopAnalyticApprox` (Grauert real-analytic approximation)

`Jacobians/RiemannSurface/SmoothAnalyticLoop.lean:175`:

```lean
def SmoothLoopAnalyticApprox (x₀ : X) : Prop :=
  ∀ (γ : ℝ → X) (hcont : Continuous γ), IsSmoothCurve γ →
    (hclosed : γ 1 = γ 0) → (hsrc : γ 0 = x₀) →
      ∃ δ : AnalyticLoop X x₀,
        Path.Homotopic (loopToPath δ) (curveToPath hcont hsrc hclosed)
```

*Every smooth loop is homotopic rel endpoints to a real-analytic
`AnalyticLoop`.*

**Why Mathlib-absent (deeper, multi-week).** Three compounding gaps:

1. **No real-analytic partition of unity / no chart-gluing for `C^ω`.** A loop
   leaves any single chart, so one cannot Fourier/Stone–Weierstrass-approximate
   in one chart's coordinates and be done; gluing `C^ω` approximations across
   overlapping charts fails because a non-constant real-analytic partition of
   unity *does not exist* (the **identity theorem** kills it). The classical
   proof needs a real-analytic embedding `X ↪ ℝ^N` and a real-analytic
   tubular-neighbourhood retraction `π`, globally approximate the loop in `ℝ^N`
   `C¹`-closely (straight-line homotopy stays in the tube, fixes the basepoint),
   then push down by `π`. **Neither the analytic embedding nor the analytic
   tubular neighbourhood is in Mathlib.**
2. **The smooth → real-analytic homotopy (Grauert 1958 / Whitney–Bruhat 1959)**
   is itself absent in any form.
3. **The `IsManifold 𝓘(ℝ, ℂ) ω X` instance is missing.** Mathlib has no
   complex-analytic ⇒ real-analytic manifold instance, so one cannot even
   *state* `ContMDiff … ω` for a curve into `X` through the real-analytic
   structure. (This file works around the *absence* by using the portable
   moving-chart `IsAnalyticCurve` predicate — `extChartAt 𝓘(ℂ)`-readout
   `ContDiffAt ℝ ω`, `SmoothAnalyticLoop.lean:90` — which needs only the
   complex-analytic structure `IsManifold 𝓘(ℂ) ω X`. The unconditional payoff
   `AnalyticLoop.ofAnalyticCurve` (`SmoothAnalyticLoop.lean:123`) shows a
   *genuinely* real-analytic loop needs no approximation at all; the wall is
   purely the production of one from a merely smooth loop.)

**Effort estimate: multi-week** (real-analytic embedding + tubular nbhd +
Grauert approximation, all absent). Confirmed multi-week and out of scope for
the wiring lane.

References: Whitney, *Differentiable manifolds*, Ann. of Math. 37 (1936);
Grauert, *On Levi's problem and the imbedding of real-analytic manifolds*,
Ann. of Math. 68 (1958); Whitney–Bruhat, Comment. Math. Helv. 33 (1959).

---

## 3. The hyperelliptic alternative (covering-space / Seifert–van Kampen route)

The {Whitney, Grauert} pair is the **general-X** route, valid for *every*
compact connected Riemann surface. For the **hyperelliptic witness family**
`y² = f(x)` there is an independent, lower-dimensional route that bypasses
analytic approximation entirely (`TGEN_ROUTE.md` §"slit-sheet lift", gap
ledger rungs D1/L1/L2):

* **D1 — PROVEN (#171).** `π₁(ℙ¹∖B)` is generated by explicit analytic circle
  lassos (`closure_circleLassos_eq_top`).
* **L1 — PROVEN (hyperelliptic).** Each lasso lifts to an analytic arc through
  the √-cover (`exists_sqrtArcData`, `Hyperelliptic/CycleLoops.lean`).
* **L2-a (index-2 kernel) — PROVEN.** General index-2 Reidemeister–Schreier
  (`Index2KernelGeneration.lean`, `closure_schreierSet_eq_ker`).
* **L2-bridge — PROVEN.** `PunctureFillData S ⟹ BranchCutGeneratesPi1 S ⟹ T-GEN`
  (`BranchCutCoveringBridge.lean`, `branchCutGeneratesPi1_of_punctureFill`).
* **L2-b — the sole residual.** Constructing one `PunctureFillData`: the
  puncture-fill **Seifert–van Kampen** surjection `π₁(X∖T) ↠ π₁(X)` plus the
  unbranched-covering identification `π₁(X∖T) ≅ ker φ`. SVK for π₁
  (free-product-with-amalgamation / groupoid pushout) is Mathlib-absent in any
  form (`CategoryTheory/Limits/VanKampen.lean` is the unrelated categorical
  notion), so this is multi-session work (`SVK_BLOCKER.md`).

So the hyperelliptic challenge is closed **modulo constructing one
`PunctureFillData`** (one SVK datum), whereas the general-X challenge is closed
**modulo {Whitney, Grauert}**. Either single named residual closes T-GEN for its
scope, hence closes `AX_PeriodCycleBasis`.

---

## 4. Headline

> **The Buzzard challenge's last axiom `AX_PeriodCycleBasis` reduces — fully
> formalized in Lean, sorry-free, with no new axiom (standard-3 only) — to two
> classical real-analytic approximation theorems that Mathlib lacks: Whitney
> (continuous ⇝ smooth) and Grauert (smooth ⇝ real-analytic), both for loops
> into a complex 1-manifold.**

The single theorem
`analyticLoopsGenerateH1_of_smoothApprox_analyticApprox`
(`TGenFinalReduction.lean`) is the composition: it takes exactly those two
theorems as hypotheses and produces T-GEN, with the `IsSmoothPath ↔
IsSmoothCurve` junction discharged by `Iff.rfl` (no hidden third wall). The
hyperelliptic family has a parallel route closed modulo a single
Seifert–van Kampen `PunctureFillData`.
