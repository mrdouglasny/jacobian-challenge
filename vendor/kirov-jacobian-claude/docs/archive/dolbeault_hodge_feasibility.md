# Feasibility & LoC estimate — a FULLY sorry-free Jacobians project

> **UPDATE 2026-06-01:** **#6 is DISCHARGED** via a standard breakpoint-perturbation route — NOT the
> de-Rham/Stokes path estimated in the (b) row below, so that #6 LoC line is moot. Frontier now **4
> deep walls**. The G3 `H¹` compactness engine (`Montel.closedBall_isCompact`) is **PROVEN in-repo**,
> so finiteness is an adaptation, not greenfield; the concentrated risk is **G4 (𝒪_D-on-manifold + Serre)**.
> Current state + RR-ladder scope: `docs/STATUS.md`.


Read-only research note for `/home/rado/jacobian`. Scopes the single analytic wall
(**Dolbeault ∂̄-solvability + de Rham/Hodge theory on a compact Riemann surface**) that the
whole open frontier (#1 genus⟺sphere, #3 Abel, #7 period full-rank, partly #6) bottoms out in.

Builds on the two prior notes (`docs/abel_riemannroch_research.md`,
`docs/riemann_roch_proof_plan.md`), re-verifying their key claims at the **current** pin and
adding fresh momentum-scan + the Radó/uniformization forks.

**Pin (confirmed this session):** Mathlib `8e3c989104daaa052921bf43de9eef0e1ac9fbf5`,
Lean `v4.30.0-rc1` — *identical* to the pin the prior notes verified against, so their
VERIFIED inventory carries over unchanged; this note re-checks the load-bearing items and the
new questions.

Legend: **[VERIFIED-NOW]** = re-confirmed this session via `lean_run_code`/`loogle`/`leansearch`/web;
**[VERIFIED-PRIOR]** = verified in the two prior notes at this same pin, not re-run now;
**[BELIEVED]** = calibrated engineering judgement / standard math, not machine-checked.

---

## 0. Bottom line (lead with the numbers)

The entire open frontier rests on **one irreducible shared analytic nugget: Dolbeault
∂̄-solvability `H¹(X,𝒪)` on a compact Riemann surface**, plus a de Rham/Hodge layer to feed
Serre duality and the Hodge–Riemann bilinear relations. **Mathlib has none of it for
manifolds, and there is no in-progress PR/project targeting manifold de Rham or Dolbeault**
(the only adjacent momentum is Euclidean-domain elliptic PDE — §1). This nugget is **~3k–6k+
LoC of greenfield manifold analysis** and **dominates every from-scratch path**.

**The strategic recommendation flips the obvious one:** because the analytic wall is so large
and unscaffolded, the **per-sorry specialized path (Path 2) is cheaper AND lower-risk than the
unified analytic-RR path (Path 1)** — *provided* one is willing to isolate the deepest
classical inputs (Abel / RR-equality) as named axioms rather than prove them. The two genuinely
*topological* forks (Radó for #7, ℂℙ¹-shim for #1) are smaller and better-scaffolded than
Dolbeault, but **neither has any Lean prior art** and both carry real formalization risk.

### 0.1 Firmed-up LoC table (per-component, with Mathlib-scaffold yes/no)

| Component | What it is | Mathlib scaffold? | LoC range | Greenfield? |
|---|---|---|---|---|
| **(a) Dolbeault ∂̄-solvability `H¹(X,𝒪)`** | the elliptic-PDE core; Forster §13–14 | **NO** (see §1) | **3000–6000+** | fully greenfield |
| ↳ prereq: Sobolev spaces on a manifold | weak derivatives, density, embedding | **NO** at manifold level (Euclidean-domain version exists *outside* Mathlib, §1.2) | (subsumed above) | greenfield |
| ↳ prereq: elliptic regularity / Fredholm / Rellich | finiteness of `H¹` | **NO** (no Fredholm-index API, no Rellich) | (subsumed above) | greenfield |
| **(b) de Rham cohomology of manifolds + homotopy invariance** (for #6) | manifold `extDeriv`, `H^k_dR`, `∫` homotopy-invariant | **PARTIAL**: `extDeriv` exists *only on normed spaces*, not manifolds (§2) | **2000–4000** | mostly greenfield |
| **(c) Hodge decomposition / harmonic representatives** | `α = harmonic + dβ + d*γ`; Hodge–Riemann relations | **NO** | **1500–3500** (on top of (a)) | greenfield |
| **(d) Serre duality / residue pairing** | `H¹(X,𝒪_D) ≅ H⁰(Ω(−D))^*` | **NO** (residue-pairing *integral* side reuses repo Green stack; analytic side rests on (a)) | **1500–3000** (on top of (a)) | greenfield analytic; repo Green stack helps the integral half |
| **Riemann–Roch (equality), assembled** | `l(D)−l(K−D)=deg D+1−g` from (a)+(d) | uses abstract homological algebra (present, §3.1) but no `𝒪_D` sheaf on a manifold | **+1000–2500** sheaf-on-manifold scaffolding + assembly | greenfield foundations |
| **ℂℙ¹ complex-manifold shim** | charted `IsManifold` on `Projectivization ℂ (Fin 2→ℂ)`, `Ω(ℙ¹)=0`, `genus ℙ¹=0`, `ℙ¹≃ₜS²` | **NO** — `Projectivization` has *no topology instance* (§4) | **300–800** | greenfield (shared #1 + #3 endgame) |
| **Radó triangulation + classification of compact surfaces** | every compact surface triangulable ⟹ standard model; topological genus | **NO** Lean prior art (§5) | **3000–8000** | fully greenfield |
| `deg(div f)=0` on a compact RS | argument principle / sum-of-residues | **NO** (no `residue`, no argument principle); repo Green stack helps | **400–900** | greenfield; repo helps |
| **#1 derivation from RR** (`l(P)=2 ⟹ deg-1 map ⟹ iso ⟹ S²`) | given RR + ℂℙ¹ shim + `deg div=0` + repo degree layer | repo `ContMDiff.degree`/`degreeFiber` present | **300–600** | derivation |
| **#3 derivation from RR** (Route B: third-kind + reciprocity) | given RR + reciprocity lemma (Green stack) + endgame | repo CutSurface/Green present | **400–900** | derivation |

**Calibration anchors (real builds, [VERIFIED-NOW]):**
- **DeGiorgi (Armstrong–Kempe, arXiv 2604.05984, Apr 2026): ~56,000 LoC** for interior
  De Giorgi–Nash–Moser regularity on **bounded Euclidean domains** — incl. the *first*
  proof-assistant Sobolev-spaces-from-weak-derivatives, Poincaré/Sobolev–Poincaré/John–Nirenberg,
  Moser iteration. **Standalone, NOT in Mathlib, NOT on manifolds, gives nothing toward
  Dolbeault/Hodge/de Rham.** This is the honest yardstick for "build the elliptic-PDE core":
  the *Euclidean* foundation alone was a multi-person, ~56k-LoC, publishable effort. A
  *manifold* Dolbeault layer needs that style of analysis re-done in charts + glued — the 3k–6k
  estimate for (a) assumes one rides a future Mathlib Sobolev/elliptic layer or builds only the
  minimal compact-surface slice, **not** the full DeGiorgi generality. If no such layer
  materialises, (a) realistically balloons toward the DeGiorgi scale.
- Mathlib's complex-analysis / Cauchy-integral build (the `Analysis.Complex.CauchyIntegral`
  stack the repo's `CutSurface` already leans on) and the manifold library both took
  multi-thousand-LoC, multi-contributor efforts — consistent with the per-component ranges.

### 0.2 Two-path totals + risk (the headline)

| | **Path 1 — unified analytic RR** | **Path 2 — specialized per-sorry** |
|---|---|---|
| **Plan** | Build (a)+(c)+(d) ⟹ prove RR-equality from scratch; use it for #1/#3/#7 | Radó for #7; ℂℙ¹-shim + RR-*consumer* for #1; trace+∂̄ **or** isolate-Abel for #3 |
| **New foundational LoC** | **~9k–18k+** (Dolbeault + Hodge + Serre + sheaf-on-manifold + RR assembly) | **~5k–11k** (Radó ~3–8k + ℂℙ¹ shim + endgames), **IF Abel/RR-equality are isolated as axioms**; **~12k–20k+ if #3's Abel is also proved** (it needs Dolbeault too) |
| **Irreducible SHARED cost** | Dolbeault (a) ~3–6k — paid once, reused by #1/#3/#7 | Dolbeault is **avoided for #7** (Radó) and **for #1** (ℂℙ¹+consumer), but **#3-by-proof still needs it**; isolating #3 removes it |
| **Risk** | **HIGH** — one giant unscaffolded analytic edifice; if Dolbeault stalls, *nothing* discharges | **MEDIUM** — risk is spread; #7-via-Radó and #1-via-shim are independent and each can succeed alone; worst case isolate #3 |
| **Sorry-free?** | Yes if (a)+(d) land | Yes for #1/#7; **#3 only if Abel is proved (⟹ Dolbeault) — otherwise #3 stays 1 isolated axiom** |

**The hard truth about "FULLY sorry-free":** a *genuinely zero-axiom* project must prove **#3
(Abel) and the RR-equality**, and **both bottom out in Dolbeault `H¹(X,𝒪)`** with no escape
(prior notes exhausted both textbook proofs of Abel; the inequality-only/Serre-free RR is a
dead leaf for #1/#3). **So a fully sorry-free project pays Dolbeault no matter what** — the only
question is whether Radó (#7) and ℂℙ¹ (#1) are *also* built (Path-2 lets #7 and #1 dodge
Dolbeault, but #3 drags it back in). **Net: the Dolbeault/Hodge wall is unavoidable for a
zero-sorry project; its ~3k–6k+ greenfield cost is the dominant term and the project's true
size driver.**

### 0.3 Recommended de-risking FIRST step

**Build the ℂℙ¹ complex-manifold shim** (`Projectivization ℂ (Fin 2→ℂ)` as a charted
`IsManifold`, with `genus ℙ¹ = 0`, `Ω(ℙ¹)=0`, `ℙ¹ ≃ₜ S²`). Rationale:
- **Smallest** of the three greenfield blockers (~300–800 LoC vs 3k+ for Dolbeault/Radó).
- **Highest fan-out**: it is the shared gate for the **#1 endgame** *and* the **#3 endgame**
  (deg-1-map ⟹ iso) *and* it is the only place either of those can even be *stated*. Both
  prior notes flag it as "the binding blocker" independent of which big theorem is chosen.
- **De-risks the consumer side** so that, whichever way the Dolbeault/RR question resolves, the
  downstream derivations are already in hand — converting "can we even use RR?" into a settled
  yes. It also forces an early answer to the `Projectivization`-has-no-topology problem (§4),
  which is a concrete, bounded Lean task (not open-ended analysis).
- Runner-up de-risking step: a **minimal ∂̄-on-a-disk lemma** (local Dolbeault, Forster §13:
  `∂̄u=f` solvable on a disc via the Cauchy transform `u(z)=(1/2πi)∬ f/(ζ−z)`). This is the
  *atom* of the entire analytic wall; proving it standalone calibrates whether the Dolbeault
  layer is 3k or 6k+, and it reuses Mathlib's existing Cauchy-integral stack. Do this **second**
  to scope (a) before committing to Path 1.

---

## 1. Q1 — Has anyone formalized Dolbeault/∂̄/Hodge/harmonic/de-Rham FOR MANIFOLDS in Lean?

**Short answer: NO for manifolds. There is fresh, directly-relevant momentum on the *Euclidean*
elliptic-PDE foundations (DeGiorgi/Sobolev), but it stops at bounded domains and is not in
Mathlib.** Verified declaration inventory:

### 1.1 What EXISTS (verified declaration names)

- **`extDeriv` (exterior derivative) — but only on a normed VECTOR SPACE, not a manifold.**
  `Mathlib.Analysis.Calculus.DifferentialForm.Basic`:
  `extDeriv (ω : E → E [⋀^Fin n]→L[𝕜] F) (x : E) : E [⋀^Fin (n+1)]→L[𝕜] F`. **[VERIFIED-NOW]**
  Companions present: `extDerivWithin_univ`, `extDeriv_extDeriv` (`d∘d=0`, with a
  `minSmoothness 𝕜 2 ≤ r` hypothesis), `extDeriv_pullback`, `Filter.EventuallyEq.extDeriv`,
  `extDeriv_constOfIsEmpty`. So Mathlib **has the flat-space exterior derivative, `d²=0`, and
  pullback** — the algebraic skeleton of de Rham — **but nothing transports it to a manifold**
  (no exterior derivative on `ContMDiffSection`s of the cotangent bundle, no `H^k_dR(M)`).
- **Abstract sheaf cohomology / homological algebra** (Joël Riou et al.): `CategoryTheory.Sheaf.H`,
  Čech complex, Mayer–Vietoris, `ShortComplex.SnakeInput`, homology LES, `HomologicalComplex.eulerChar`,
  skyscraper sheaves, `Ext`/right-derived functors. **[VERIFIED-PRIOR]** — all present, all
  *abstract*; there is nothing on a complex manifold to apply them to.
- **Liouville on compact complex manifolds:** `MDifferentiable.exists_eq_const_of_compactSpace`
  (gives `H⁰(X,𝒪)=ℂ`). **[VERIFIED-PRIOR]**
- **Planar complex analysis:** `MeromorphicOn.divisor`, `extract_zeros_poles`, box-Cauchy
  `integral_boundary_rect_eq_zero_of_differentiableOn`, single-residue Cauchy brick. **[VERIFIED-PRIOR]**
- `TopCat`, `FundamentalGroup` (π₁) exist. **[VERIFIED-NOW]**

### 1.2 What is ABSENT (honest list)

- **Dolbeault / ∂̄-solvability / `H^{0,1}` / `H¹(X,𝒪)`** — *nothing*. No `Dolbeault`, no `dBar`.
  **[VERIFIED-PRIOR]**
- **de Rham cohomology of a MANIFOLD** (`H^k_dR(M)`, de Rham theorem `≅` singular cohomology) —
  *nothing*. `leansearch "de Rham cohomology of a smooth manifold ≅ singular cohomology"`
  returns only group cohomology / continuous-group cohomology / cotangent-`H1` — none of it
  manifold de Rham. **[VERIFIED-NOW]**
- **Singular homology/cohomology of a topological space** (`H_n(X)`, `H^n(X)`) — *absent*.
  `#check @singularHomology` → **unknown identifier**. **[VERIFIED-NOW]** (Mathlib has π₁ and
  *abstract* simplicial/chain machinery + a simplicial-homology *work-in-progress*, but no
  `H_*` functor for spaces, hence no homotopy invariance of integrals for #6.)
- **Hodge theory / harmonic forms / Hodge decomposition / Hodge–Riemann relations** — *absent*.
  **[VERIFIED-PRIOR + NOW]** (web scan: "Hodge decomposition … still missing in Mathlib").
- **Elliptic operators on manifolds, Fredholm index, Rellich compactness, Sobolev spaces on a
  manifold** — *absent*. **[VERIFIED-PRIOR]**
- **Serre duality, Riemann–Roch (any form), coherent sheaves, structure sheaf on a complex
  manifold, `𝒪_D`, residue theorem / argument principle / `deg(div f)=0`** — *absent*.
  **[VERIFIED-PRIOR]**
- **Complex ℂℙ¹ as a manifold** — *absent* (`Projectivization` has no topology, §4). **[VERIFIED-PRIOR]**

### 1.3 Momentum scan — is anyone heading toward manifold de Rham / Dolbeault?

**Verdict: there is elliptic-PDE momentum, but it is Euclidean and external; no manifold de
Rham / Dolbeault / Hodge effort is visible.** [VERIFIED-NOW]

- **DeGiorgi — Scott Armstrong & Kempe, "Formalization of De Giorgi–Nash–Moser Theory in Lean"
  (arXiv 2604.05984, April 2026; repo `github.com/scottnarmstrong/DeGiorgi`).** ~**56,000 LoC**,
  **standalone (not Mathlib)**. Builds: **Sobolev spaces on bounded domains from weak
  derivatives** (first proof-assistant instance at this generality), weak formulation of
  divergence-form elliptic PDE, Poincaré / Sobolev–Poincaré / John–Nirenberg, De Giorgi & Moser
  iteration, Harnack + Hölder regularity. **Explicitly: bounded Euclidean domains only; NO
  manifolds, NO Fredholm, NO Dolbeault/Hodge/de Rham.** This is the closest thing to
  "prerequisites for the elliptic core" and it is (i) not in Mathlib, (ii) not on manifolds.
  *Relevance:* if this lands in Mathlib and is extended to manifolds, it would be the substrate
  for Dolbeault finiteness/regularity — but that is future, large, and uncommitted.
- **Cohomology theories in Mathlib** (Banff workshop blog; derived categories paper afm 15978):
  active on *algebraic/abstract* cohomology (group, sheaf, derived cats), **de Rham of manifolds
  explicitly named as "not yet formalized."** [VERIFIED-NOW]
- **Hodge theory for the Hodge-conjecture Millennium write-up** (lean-dojo
  `LeanMillenniumPrizeProblems`): notes singular cohomology of complex varieties, cycle class
  map, and Hodge decomposition are **still missing**. [VERIFIED-NOW]
- **`extDeriv` on normed spaces** (`Analysis.Calculus.DifferentialForm`) is the one genuine
  toe-hold: a future "extDeriv on manifolds + `H^k_dR`" PR could build on it, but **none is
  in progress** (no PR found; community discussions report "no concrete progress" on manifold
  differential forms). [VERIFIED-NOW]

**Bottom line Q1:** the analytic wall is greenfield for manifolds. The *only* relevant 2026
momentum (DeGiorgi Sobolev/elliptic) is Euclidean, external, and would itself need a manifold
lift before it could feed Dolbeault. **Plan around Mathlib having none of (a)–(d).**

---

## 2. Q2 — Realistic LoC for the minimal analytic foundation a compact-RS Riemann–Roch needs

Per-component, calibrated to the table in §0.1 and the DeGiorgi/complex-analysis anchors.

### (a) ∂̄/Dolbeault solvability `H¹(X,𝒪)` — the elliptic-PDE core. **3000–6000+ LoC. Greenfield.**
- **Mathlib prerequisites present? NO.** No Sobolev spaces (manifold or even in-Mathlib
  Euclidean — DeGiorgi's are external), no elliptic regularity, no Fredholm, no Rellich. The
  *local* atom — `∂̄u=f` on a disc via the Cauchy transform (Forster §13.2) — is the one piece
  that reuses existing Mathlib Cauchy-integral machinery and is ~**200–500 LoC** alone; the rest
  (patching local solutions, finiteness of `H¹` via a Montel/Schwartz compactness argument on
  Čech cochains, Forster §14.9) is the bulk and is unscaffolded. The repo's `Montel.lean` (Montel
  for *global* `Ω(X)`) is morally adjacent but operates on a different space — technique
  transfers, lemma does not. **[VERIFIED-PRIOR]**
- *Calibration:* Euclidean Sobolev+elliptic alone = ~56k LoC (DeGiorgi). The 3–6k figure assumes
  one builds only the **minimal compact-RS slice** (one elliptic operator `∂̄`, finiteness via
  Montel rather than general Fredholm) and/or rides a future Mathlib Sobolev layer. **Without a
  Sobolev substrate, realistically toward the high end / beyond.** [BELIEVED]

### (b) de Rham cohomology of manifolds + homotopy invariance of period integrals (for #6). **2000–4000 LoC. Mostly greenfield.**
- **Scaffold? PARTIAL.** `extDeriv`+`d²=0`+pullback exist **on normed spaces** [VERIFIED-NOW] —
  these are the local models; lifting to a manifold (exterior derivative of a `ContMDiffSection`
  of `⋀ᵏ T*M`, well-definedness across charts, `H^k_dR := ker d / im d`) is greenfield. **Homotopy
  invariance of `∫_γ ω` for closed `ω`** (the piece #6 wants) is the de Rham / Stokes-on-a-homotopy
  argument; Mathlib has **no manifold Stokes** in general (the repo only has box/cut Stokes), and
  **no singular homology** to phrase "homologous cycles." [VERIFIED-NOW] So #6's homotopy
  invariance is either a focused ~**800–1500 LoC** Stokes-on-a-cylinder lemma (cheaper, repo-style)
  or part of a full de Rham build (the 2–4k figure). [BELIEVED]

### (c) Hodge decomposition / harmonic representatives. **1500–3500 LoC on top of (a). Greenfield.**
- **Scaffold? NO.** Needs (a)'s elliptic theory (the Laplacian `Δ=∂̄*∂̄+∂̄∂̄*`, ellipticity,
  finite-dim kernel = harmonic forms) plus the orthogonal `L²` decomposition. This is where the
  **Hodge–Riemann bilinear relations** for #7's analytic route live. Entirely greenfield;
  strictly *more* than (a) since it needs (a) first. [BELIEVED]

### (d) Serre duality / residue pairing. **1500–3000 LoC on top of (a). Greenfield analytic; repo Green stack helps the integral half.**
- **Scaffold? Partial-but-deep.** The pairing's *topological/integral* side — sum-of-residues=0,
  reciprocity bookkeeping — **is the same cut-surface + box-Green computation the repo already
  built for R1/R2** (`CutSurface`, `boundaryForm`, `EdgeChangeOfVariables`, `GreenPositivity`).
  [VERIFIED-PRIOR] That is a genuine partial down-payment. **But** the *analytic* side
  (perfectness of the pairing, `H¹(X,𝒪_D) ≅ H⁰(Ω(−D))^*`) rests on (a) Dolbeault and has no
  scaffold. [BELIEVED]

### RR assembly + sheaf-on-a-manifold foundations. **+1000–2500 LoC. Greenfield foundations.**
- The skyscraper SES `0→𝒪_D→𝒪_{D+P}→ℂ_P→0`, the `χ`-additivity induction, and the
  Euler-characteristic bookkeeping are **elementary given the objects, and Mathlib's abstract
  homological algebra can run them** (snake lemma, LES, `eulerChar` — all present [VERIFIED-PRIOR]).
  **The blocker is that `𝒪_D` / `H^i(X,𝒪_D)` do not exist on a complex manifold** — there is no
  structure sheaf on a manifold to build them. [VERIFIED-PRIOR] So the "cheap middle" of Forster's
  proof is *unreachable* without first building the sheaf-cohomology-of-a-complex-manifold layer,
  which is itself ~1–2.5k LoC and larger than building (a) directly — hence **do not pursue RR via
  the from-scratch Forster sheaf route.**

**Q2 total for a from-scratch analytic RR foundation:** `(a)+(c or d)+RR-assembly` ≈
**~6k–12k+ LoC of greenfield manifold analysis**, dominated by (a) and the sheaf-on-manifold
layer, with essentially no Mathlib scaffolding to amortize against. Calibrated against the ~56k
Euclidean-only DeGiorgi effort, this is *optimistic* and assumes a minimal-slice build.

---

## 3. Q3 — The #7 fork: Hodge route vs Radó route

#7 = "the period lattice is a full-rank ℝ-lattice." Two routes:

**(i) Analytic / Hodge route** — via the Hodge–Riemann bilinear relations (R1/R2 plus
positivity), needing the Dolbeault/de Rham/Hodge foundation (a)+(c). This would *supersede* the
repo's current cut-surface route. **Cost:** the full (a)+(c) wall, **3k–6k+ on top of what's
there**. Only worth it if Dolbeault is being built anyway (Path 1).

**(ii) Cut-surface + Radó triangulation + surface classification** — the repo's **current**
route. The analytic part (R1/R2 via `CutSurface`/box-Green) is **already done and axiom-clean**
(`cutSurface_R1`, R2 sign fixed, `EdgeChangeOfVariables` — per recent commits). **What remains
is purely topological:** a canonical dissection / standard `4g`-gon model of the surface, which
classically comes from **Radó's triangulation theorem + the classification of compact surfaces**.
The repo isolates this as `exists_canonicalDissection` / `exists_cutSurface`.

### 3.1 Has anyone formalized Radó / classification of compact surfaces in Lean?

**NO. [VERIFIED-NOW]** Web + Lean searches find **no** Lean 4 / Mathlib formalization of Radó's
triangulation theorem or the classification of compact surfaces. Mathlib has only
`Analysis.Convex.SimplicialComplex` (geometric simplicial complexes for *convex geometry*) and a
*simplicial-homology work-in-progress* — **no abstract simplicial complexes glued to manifolds,
no triangulation-of-a-surface, no genus-of-a-topological-surface, no classification theorem.**
There is no `FundamentalGroup`-beyond-π₁ homology to even state the invariants. So route (ii)'s
topological core is **fully greenfield** in Lean.

### 3.2 LoC + risk of route (ii)

- **Radó triangulation (every compact surface is triangulable):** classically delicate (needs
  Jordan–Schoenflies-type input; Mathlib has Jordan curve theorem? — *not* in a usable
  triangulation form). **~2000–5000 LoC. HIGH risk** (point-set-topology-heavy, the kind of proof
  that balloons in formalization; few have even attempted it in any prover). [BELIEVED]
- **Classification of compact surfaces (⟹ standard `4g`-gon / canonical dissection):** the
  combinatorial edge-word normalization (Brahana/Conway "ZIP" proof) is ~**1000–3000 LoC**,
  **MEDIUM risk** (combinatorial, but long and fiddly; no Lean prior art). [BELIEVED]
- **Total route (ii) topology: ~3k–8k LoC, MEDIUM–HIGH risk.**

### 3.3 Is (ii) cheaper/safer than building Dolbeault, given Dolbeault is needed for #1/#3 anyway?

**Nuanced — this is the crux of the strategic question:**
- **For #7 in isolation:** route (ii) (~3–8k topology) is **comparable in LoC** to Dolbeault
  (~3–6k) and is **arguably *higher* risk** (Radó triangulation is a notorious formalization
  tar-pit; Dolbeault is "just" hard analysis with a clear local atom). The repo has *already
  paid the analytic half* of (ii), so the *marginal* cost of (ii) is only the topology — which
  tilts (ii) cheaper **for #7 specifically**.
- **But Dolbeault is allegedly "needed for #1/#3 anyway."** This is **only half-true**:
  - **#1** can dodge Dolbeault via the **ℂℙ¹-shim + RR-*consumer*** route — *if* RR-equality is
    *isolated as an axiom* (then #1 needs no Dolbeault, just the shim + degree endgame).
  - **#3** genuinely needs Dolbeault **only if Abel is proved**; **isolating Abel removes it.**
  - So Dolbeault is **needed for a fully-sorry-free project** (to prove Abel and/or RR-equality),
    but **not needed if those two are kept as isolated classical axioms.**
- **Therefore:** if the goal is *fully sorry-free*, Dolbeault is unavoidable and route (ii)'s
  topology is **extra** cost on top — making the **Hodge route (i) the LoC-efficient choice for
  #7** (reuse the Dolbeault you must build anyway). If the goal tolerates **isolated axioms for
  Abel/RR**, then **route (ii) lets #7 become genuinely sorry-free without Dolbeault**, and is
  the right call for #7 — at the price of MEDIUM–HIGH topological risk.

**Recommendation for #7:** if pursuing *fully sorry-free*, do #7 via the Hodge route as a
byproduct of the Dolbeault build (route i). If pursuing *minimal-axiom* (isolate Abel/RR), keep
the repo's route (ii) but **treat Radó as the project's single highest-risk item** — and
seriously consider keeping `exists_canonicalDissection` *itself* isolated (status quo, 0 LoC),
since Radó is as hard to formalize as anything here.

---

## 4. Q4 — The #1 fork: RR vs uniformization

#1 = "genus 0 ⟹ X ≅ sphere." Two routes:

**(A) Riemann–Roch route:** `genus 0 ⟹ l(P)=2 ⟹` non-constant function with one simple pole
`⟹` degree-1 map `X→ℙ¹ ⟹` biholomorphism `⟹ X≃ₜS²`. Needs: RR-equality (isolatable) + **ℂℙ¹
shim** + `deg(div f)=0` + repo degree layer + Liouville (present).

**(B) Uniformization route:** via the uniformization theorem (genus 0 simply-connected RS ≅ ℂℙ¹),
itself proved via potential theory / the Riemann mapping theorem generalized to surfaces.

### 4.1 Uniformization / RMT formalization status

- **Riemann Mapping Theorem (classical, simply-connected open `U ⊊ ℂ`):** there is a substantial
  standalone Lean 4 project, **`vbeffara/RMT4`** (Vincent Beffara, 276 commits, ~96% Lean), which
  formalizes the classical RMT and has been the basis for upstreaming RMT pieces. [VERIFIED-NOW
  that the repo exists, is Lean-4, active; exact sorry-count not re-confirmed this session — treat
  "classical RMT essentially done in RMT4" as [BELIEVED] from its standing in the community.]
- **Crucially, RMT4 / Mathlib cover only the *planar* RMT** (biholomorphism between
  simply-connected proper open subsets of ℂ). **The *uniformization theorem for abstract Riemann
  surfaces* — which is what #1 route (B) needs — is NOT formalized** anywhere in Lean, and is a
  far deeper result (potential theory / Perron's method / the full Koebe uniformization).
  [VERIFIED-NOW — no Lean uniformization-of-surfaces found.]
- **ℂℙ¹ as a complex manifold is itself absent** (`Projectivization ℂ (Fin 2→ℂ)` has *no*
  `TopologicalSpace`/`ChartedSpace ℂ`/`IsManifold` instance — `infer_instance` fails).
  [VERIFIED-PRIOR] So *both* routes (A) and (B) need the ℂℙ¹ shim built first.

### 4.2 LoC + risk

- **Uniformization route (B): VERY HIGH risk, very large.** Uniformization-of-surfaces is one of
  the deepest theorems in the area; its potential-theory proof (subharmonic functions, Perron
  families, Green's functions on a surface, the regularity of the solution) is **easily ~5k–15k
  LoC greenfield**, and it would *still* need the ℂℙ¹ shim. Mathlib's planar RMT does **not**
  shorten it materially (the surface case is a different, harder argument). **Not recommended.**
- **RR route (A): LOWER risk, smaller.** Given RR-equality isolated + ℂℙ¹ shim (~300–800) +
  `deg(div f)=0` (~400–900) + repo `ContMDiff.degree`/`degreeFiber` (present), the #1 derivation
  is ~**300–600 LoC**, **MEDIUM risk** (the deg-1-map-⟹-iso endgame is standard and the repo has
  the degree layer). The deep input (RR-equality) is shared with #3 and isolatable.

### 4.3 Which is more standard / lower-risk?

**The RR route (A) is more standard, lower-risk, and far smaller** — *and* it reuses the ℂℙ¹
shim and degree layer the repo is already oriented around. **Uniformization is the wrong tool to
formalize here** (deeper than RR, no Lean prior art for the surface case, no LoC savings). The
*only* caveat: route (A) needs RR-equality, which (if proved not isolated) drags in Dolbeault —
but #1 can consume RR-equality as an *isolated axiom* and remain locally sorry-free.

**Recommendation for #1:** RR route (A), consuming an isolated RR-equality, gated on the ℂℙ¹
shim (the §0.3 first step). Avoid uniformization entirely.

---

## 5. Q5 — Bottom line for the two strategic paths

### Path 1 — prove analytic RR (+ its Dolbeault foundation), use for #1/#3/#7
- **New foundational LoC: ~9k–18k+** = Dolbeault (a) 3–6k + Hodge (c) 1.5–3.5k + Serre/residue
  (d) 1.5–3k + sheaf-on-manifold + RR assembly 1–2.5k + #1/#3/#7 derivations 1–2k + ℂℙ¹ shim
  0.3–0.8k. **Calibrated low** against DeGiorgi's 56k Euclidean-only; realistically toward the
  high end if no Sobolev substrate lands.
- **Shared cost:** Dolbeault (a) paid once, reused by all of #1/#3/#7 (via RR + Hodge).
- **Risk: HIGH.** One monolithic unscaffolded analytic edifice; a stall in (a) blocks
  *everything*. Single biggest formalization bet in the project.
- **Sorry-free payoff:** if (a)+(d) land, **all four sorries discharge with zero axioms** — the
  cleanest possible end state. This is the only path to a *genuinely* zero-axiom project.

### Path 2 — specialized per-sorry
- **#7 via Radó** (route ii): ~3–8k topology, MEDIUM–HIGH risk — *or* keep
  `exists_canonicalDissection` isolated (0 LoC).
- **#1 via ℂℙ¹-shim + isolated-RR-consumer:** ~0.6–1.5k, MEDIUM risk.
- **#3 via isolated-Abel + endgame:** ~0.3–0.5k derivation on 1 isolated Abel axiom (prior note
  §5.1) — *or* prove Abel ⟹ pays Dolbeault (back to Path 1's wall).
- **#6** (homotopy invariance / preimage-cycle): focused Stokes-on-a-cylinder ~0.8–1.5k, or
  isolate.
- **New foundational LoC: ~5k–11k IF Abel/RR-equality are isolated as axioms**;
  **~12k–20k+ if #3's Abel is proved** (Dolbeault returns).
- **Shared cost:** Dolbeault **avoided for #7 (Radó) and #1 (shim+consumer)**; **returns only if
  #3 is proved**. The ℂℙ¹ shim is the shared piece across #1/#3 endgames.
- **Risk: MEDIUM, spread.** Each sorry is an independent bet; #7-Radó and #1-shim can each
  succeed alone; worst case any one stays isolated. No single point of total failure.

### The irreducible shared cost & which path is lower-risk
- **Irreducible for a *fully sorry-free* project: Dolbeault `H¹(X,𝒪)` (~3–6k+, greenfield).**
  Both Abel and RR-equality bottom out in it; the inequality-only RR is a dead leaf for #1/#3
  (prior note §3/§7). **No zero-axiom project escapes Dolbeault.**
- **Lower-risk path: Path 2 (specialized), with risk *spread* and the option to isolate the two
  deepest inputs (Abel, RR-equality).** Path 1 concentrates all risk in one giant analytic build.
- **BUT** for a *genuinely zero-axiom* end state, Path 1 is the only one that gets there
  *cleanly* (Path 2 needs Dolbeault for #3 anyway, at which point you've half-built Path 1). The
  honest framing: **Path 2 minimizes risk-to-first-results and lets #7/#1 go sorry-free without
  Dolbeault; Path 1 is the only route to ALL-four-sorry-free-with-no-axioms, at maximal risk.**

### Recommended de-risking FIRST step (restated)
**Build the ℂℙ¹ complex-manifold shim** (`Projectivization ℂ (Fin 2→ℂ)` charted-manifold +
`Ω(ℙ¹)=0`, `genus ℙ¹=0`, `ℙ¹≃ₜS²`). It is the **smallest** greenfield blocker (~300–800 LoC),
**unblocks both the #1 and #3 endgames**, is a **bounded, concrete Lean task** (not open-ended
analysis), and de-risks the consumer side regardless of how the Dolbeault/RR question resolves.
**Then** (second) prove the **minimal ∂̄-on-a-disk lemma** to scope whether the Dolbeault layer
is 3k or 6k+ before committing to Path 1. Defer Radó and full Dolbeault until these two cheap
probes have set the cost.

---

## 6. Status separation & sources

**VERIFIED-NOW (this session, pin `8e3c989` / `v4.30.0-rc1`):**
- `extDeriv` exists on normed spaces only (`Analysis.Calculus.DifferentialForm.Basic`); `d²=0`,
  pullback present; **no manifold version** — `loogle "extDeriv"`, `lean_run_code`.
- `singularHomology` unknown identifier; no manifold de Rham / singular cohomology — `lean_run_code`,
  `leansearch`.
- `TopCat`, `FundamentalGroup` exist — `lean_run_code`.
- **DeGiorgi** (arXiv 2604.05984; `github.com/scottnarmstrong/DeGiorgi`): ~56k LoC, standalone,
  Sobolev-on-bounded-Euclidean-domains + elliptic regularity, **no manifolds/Fredholm/Dolbeault** —
  WebFetch of the author's blog post.
- **RMT4** (`github.com/vbeffara/RMT4`): standalone Lean-4 classical RMT, 276 commits; covers
  **planar** simply-connected RMT, **not** surface uniformization — WebSearch/WebFetch (exact
  sorry-count not re-confirmed; standing as "classical RMT done" is [BELIEVED]).
- **No Lean Radó / surface-classification**; Mathlib has only `Analysis.Convex.SimplicialComplex`
  + WIP simplicial homology — WebSearch + `leansearch`.
- Community/momentum: de Rham of manifolds + Hodge decomposition explicitly named as **not yet
  formalized** (Banff cohomology blog; LeanMillenniumPrizeProblems) — WebSearch.

**VERIFIED-PRIOR (at this same pin, in `docs/abel_riemannroch_research.md` &
`docs/riemann_roch_proof_plan.md`):** the full ABSENT list (Dolbeault, Serre, RR, coherent
sheaves, structure sheaf on a manifold, `𝒪_D`, residue theorem, `deg(div f)=0`, complex ℂℙ¹);
the PRESENT abstract-homological-algebra toolkit; Liouville on compact manifolds; planar
meromorphic divisors; the repo asset inventory (Montel, CutSurface/Green R1/R2, Trace,
`ContMDiff.degree`/`degreeFiber`, manifold meromorphic divisor).

**BELIEVED (engineering judgement / standard math):** all LoC ranges; the Radó/uniformization
risk gradings; that Abel and RR-equality both bottom out in Dolbeault (proved by the prior notes
exhausting both textbook routes); that the inequality-only RR is a dead leaf for #1/#3.

**Web sources:**
- Armstrong–Kempe, *Formalization of De Giorgi–Nash–Moser Theory in Lean* —
  https://www.scottnarmstrong.com/2026/04/formalizing-de-giorgi-nash-moser-theory-in-lean/ ,
  https://arxiv.org/pdf/2604.05984 , https://github.com/scottnarmstrong/DeGiorgi
- LeanMillenniumPrizeProblems — https://github.com/lean-dojo/LeanMillenniumPrizeProblems
- Banff "Formalising cohomology theories" — https://leanprover-community.github.io/blog/posts/banff-cohomology/
- RMT4 — https://github.com/vbeffara/RMT4
- Mathlib `My 100 theorems` (RMT listed as wanted) — https://github.com/leanprover-community/mathlib4/issues/6091
- Mathlib `Analysis.Convex.SimplicialComplex.Basic` docs —
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Convex/SimplicialComplex/Basic.html

**Repo / prior notes:** `docs/abel_riemannroch_research.md`, `docs/riemann_roch_proof_plan.md`,
`docs/period_lattice_realbasis_research.md`, `docs/STATUS.md`; `lake-manifest.json`,
`lean-toolchain` (pin confirmation).
