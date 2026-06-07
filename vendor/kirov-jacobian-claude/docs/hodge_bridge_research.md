# Research — the Hodge/Serre bridge `H^{0,1}(X) ≅ Ω(X)` (the gate for `arithmeticGenus_eq_genus`)

Read-only scoping note for `/home/rado/jacobian`. Companion to `docs/architecture_map.md`,
`docs/abel_riemannroch_research.md`, `docs/period_lattice_realbasis_research.md`. Verified against
the repo's Mathlib pin (`8e3c989…`) and this session's capability survey.

Legend: **[VERIFIED]** read off Mathlib/repo this session; **[BOOK]** Forster/Griffiths–Harris;
**[BELIEVED]** standard, not re-derived.

---

## 🚩 FRESH SESSION: START HERE → jump to "## EXECUTION PLAN" at the bottom of this file.
This doc is the **self-contained build plan** for the PDE-free Serre/RR path (the gate for the forward
headline `genus_eq_zero_iff_homeo`). Read the CORRECTION (next) for the key finding, then the EXECUTION
PLAN for what to build, in what order, reusing which files. Constraint: **no isolated/"modulo" kernel
sorries as a deliverable; OK to prove weaker (conditional / one-directional / inequality) statements
genuinely sorry-free.** RT2 (the Dolbeault comparison, `DolbeaultComparisonEquiv.lean:245`) is deferred —
do the Serre/RR path first to de-risk and establish it.

## ✅ PROGRESS (2026-06-03): §17.9 litmus test PASSED + leaf statements verified vs Forster

Read Forster §17.1–17.14 directly (PDF pp. 138–146). Two concrete results this session:

**1. The §17.9 "formalizability litmus test" PASSED — axiom-clean.** The PDE-free route's keystone claim
is that Serre surjectivity (`ι_D` onto) is *pure finite-dim linear algebra*. Confirmed by formalizing the
two content-free abstractions of Forster's pigeonhole, both sorry-free + axiom-clean
(`Jacobians/Dolbeault/SerreDuality.lean`, builds in 9s, commit `ff54bf8`):
  - `subspaces_inf_ne_bot_of_finrank_add_gt` — `dim Λ + dim W > dim V ⟹ Λ ⊓ W ≠ ⊥` (via Mathlib
    `Submodule.finrank_sup_add_finrank_inf_eq`). This is Forster's `Λ ∩ Im ι_{D_n} ≠ 0`.
  - `serre_surjectivity_dim_core` — the full "for `n` sufficiently large,
    `dim Λ_n + dim Im ι_{D_n} > dim H¹(𝒪_{D_n})*`" count, parametrized by the Riemann–Roch dimension
    bounds (17.4/17.8) as hypotheses. The needed inequality is `n + 2 − 2g + k₀ > 0` (Forster's bounds:
    `dimΛ ≥ 1−g+n`, `dim Im ι ≥ n+k₀−d`, `dim V = n+g−1−d`), so any `n > max(d, 2g−2−k₀)` works.
  - **Conclusion:** §17.9 formalizes cleanly *given* the cohomology objects + maps. The wall is NOT in
    the duality argument; it is in *building* `H¹(𝒪_{D_n})`, `H⁰(𝒪_{nP})`, `ι_D`, and the 17.8 `ψ`-action,
    then *instantiating* `serre_surjectivity_dim_core`. That is the real PHASE-0 work (non-trivial but
    PDE-free). See the file's header docstring for the instantiation map.

**2. Leaf statements are faithful to Forster (resolves the soundness-audit `serre_h1_eq` worry).**
  - `arithmeticGenus_eq_genus : h1Dim 0 = genus X` ✓ — Forster 17.10 `g = dim H¹(X,𝒪) = dim H⁰(X,Ω)`,
    and `genus X := dim Ω(X)`. (Needs the `IsLeray` hyp so `cechH1` computes the true `H¹` — present.)
  - `serre_h1_eq : ∃ K, ∀ D, h1Dim D = lDim (K−D)` ✓ — Forster 17.11 + 17.4 + 17.10 give
    `dim H¹(𝒪_D) = dim H⁰(Ω_{−D}) = dim H⁰(𝒪_{K−D}) = l(K−D)` with `K=(ω)` a *single* canonical divisor.
    The `∃K ∀D` order (K fixed before D) is exactly Forster — **not** the unsound "free-K" form the audit
    flagged; the current statement is correct as written.

**Key dependency confirmed while reading §17:** the Čech-residue `Res : H¹(X,Ω)→ℂ` (17.2 local-residue
sum, the PDE-free substitute for 17.1's `∬_X`) needs the residue theorem `∑Res=0` for its
*well-definedness on cohomology classes* — i.e. PHASE-0's `Res` depends on PHASE-2's `deg_div`. So either
thread `∑Res=0` as a hypothesis through Phase 0, or do `deg_div` first. (Forster avoids this by using the
17.1 `∬_X` definition + 17.3 Stokes; we trade Stokes for the residue theorem.)

## ⚠ CORRECTION (2026-06-03, after reading Forster §16–19 directly)

**The earlier draft of this doc (below §0) wrongly claimed the hard direction's "irreducible core is
Weyl's lemma / elliptic regularity." That is FALSE.** It described the *Hodge-harmonic* route
(Griffiths–Harris), which we do **not** need and should **not** take. Reading Forster's *complete* Serre
Duality proof (§17.1–17.12) settles it:

**Serre duality (§17) and Riemann–Roch (§16) are proved BEFORE and WITHOUT the harmonic-forms machinery
(§19).** Forster's §19 (`*`-operator, harmonic forms, the L² scalar product `∬ω∧*ω̄` — the elliptic/Hodge
content) is used ONLY to prove genus is a *topological* invariant. **Serre/RR are entirely PDE-free.**

The actual ingredients of Serre duality's hard direction (§17.9 surjectivity):
| Ingredient | Kind | Repo |
|---|---|---|
| Finiteness `dim H¹<∞` (§14) | functional analysis (Montel + Schwartz compact-perturbation lemma) | ~95% reuse + Schwartz lemma; `exists_cechModel` open |
| `Res: H¹(X,Ω)→ℂ` via Mittag–Leffler / **sum of local residues** (§17.2) | holomorphic residue algebra | residue/`deg_div` machinery |
| Residue theorem `∑Res=0` (Res well-defined on classes) | Stokes-on-X **or** the repo's degree route | `deg_div` (degree route, PDE-free) |
| Riemann–Roch dimension counts (§16) | finiteness + skyscraper SES | `cohomological_RR` (mod skyscraper) |
| §17.9 surjectivity | **finite-dim linear algebra** (pigeonhole `dimΛ+dimIm>dim ⇒ ∩≠∅`) | trivial in Lean |

No harmonic forms, no Weyl, no elliptic regularity, no ∂̄-Laplacian, no manifold 2-form integration
(the Čech-residue route defines `Res` via local residues, getting well-definedness from `∑Res=0`, per
§17.2 — sidestepping the §17.3 Stokes identity). **It is a large but PDE-free, functional-analytic +
holomorphic-algebraic build — a fundamentally more tractable risk class than "Hodge from scratch."**

The §2 EASY/HARD (conjugation + L² positivity) decomposition below describes the **Hodge route** and is
moot for the recommended Forster route (the positivity is used by #7 and §19, not by Serre duality).

---

## 0. Bottom line (ORIGINAL DRAFT — superseded by the correction above on the PDE question)

**The headline (`genus_eq_zero_iff_homeo`, forward) bottoms out in Serre duality at `D=0`.** ~~Mathlib has
zero scaffolding... research-scale analysis...~~ — see the correction: it is PDE-free (Forster §16–17),
gated on finiteness (functional analysis) + the residue/RR machinery, not on Hodge/elliptic.

**The target `arithmeticGenus_eq_genus : h1Dim 0 = genus` splits into two very unequal halves:**

| Half | Statement | Cost | Reuses |
|---|---|---|---|
| **EASY** | `genus ≤ h1Dim 0` | ~shared with #7 (2–4k LoC, partly built) | the #7 cut-surface/Green/`CurveIntegral` engine + the L² positivity `(i/2)∮ω∧ω̄>0` |
| **HARD** | `h1Dim 0 ≤ genus` | research-grade, multi-month, **the wall** | nothing in Mathlib; the repo's finiteness + comparison help but don't close it |

**Recommended posture:** keep `arithmeticGenus_eq_genus` (and `serre_h1_eq`) as **named honest kernels**
— the project has *already* achieved the defensible milestone "challenge API + RR ladder complete modulo
a handful of named classical-theorem inputs (Serre duality, residue theorem, Abel)." If a real discharge
is wanted, **invest in the EASY half first** (it is mostly the #7 build, unlocks part of #7 and #1b too),
and isolate the HARD half as the single kernel `serre_pairing_perfect`. Do **not** attempt full
Hodge-Laplacian decomposition — it is strictly larger and equally unscaffolded.

---

## 1. The exact target and why the comparison alone is not enough

`genus X := Module.finrank ℂ (HolomorphicOneForms X)` (`Genus.lean`); `HolomorphicOneForms X` = analytic
sections of the cotangent bundle (`HolomorphicForms.lean`), finite-dim (Montel). [VERIFIED]

`arithmeticGenus_eq_genus (𝔘) (hL) : 𝔘.h1Dim 0 = genus X` where `h1Dim 0 = finrank ℂ (cechH1 𝔘 0)`.

The Dolbeault comparison (`cechH1_dolbeault_comparison`, this session: round-trip 1 + crux done,
round-trip 2 scoped) gives only
```
finrank ℝ (DolbeaultH01 X) = 2 · finrank ℂ (cechH1 𝔘 0) = 2 · h1Dim 0.
```
This relates `cechH1` to the Dolbeault `H^{0,1}` — it is **`H¹(𝒪) ≅ H^{0,1}`**, the *first* iso of the
classical chain `H¹(𝒪) ≅ H^{0,1} ≅ Ω(X)*`. By itself it yields the **tautology** `2·h1Dim = 2·h1Dim`.
To reach `h1Dim 0 = genus` we additionally need the **second** iso
```
finrank ℝ (DolbeaultH01 X) = 2 · genus X      i.e.   dim_ℂ H^{0,1}(X) = dim_ℂ Ω(X) = g,
```
which is **Serre duality at `D=0`** (equivalently the Hodge fact `H^{0,1} ≅ conjugate of Ω`). This is
the bridge this note scopes.

(Note: `DolbeaultH01 X` is built as a `Module ℝ` only; its natural `Module ℂ` — the pointwise codomain
action — is part of the bridge build, needed to phrase `dim_ℝ = 2·dim_ℂ`. Minor, ~tens of LoC.)

---

## 2. The two-direction decomposition (the precise math)

The natural map is the **conjugation** `Φ : Ω(X) → H^{0,1}(X)`, `ω ↦ [ω̄]` (a holomorphic `(1,0)`-form's
conjugate is a `∂̄`-closed `(0,1)`-form; on a curve `A^{0,2}=0` so every `(0,1)`-form is a class). `Φ`
is **conjugate-ℂ-linear**. Serre duality at `D=0` ⟺ `Φ` is a (conjugate-linear) **isomorphism**.

### 2a. EASY half — `Φ` injective ⟹ `g ≤ dim_ℂ H^{0,1}` [shared with #7]

`Φ(ω)=0` means `ω̄ = ∂̄f` for some smooth `f`. Then
```
∫_X ω̄ ∧ ω = ∫_X (∂̄f) ∧ ω = ∫_X d(f·ω) = 0      (Stokes; ω holomorphic ⟹ dω = ∂ω, and (∂f)∧ω is (2,0)=0)
```
but the **L² positivity** `(i/2)∫_X ω̄∧ω = ∫_X |coeff|² dA > 0` for `ω ≠ 0`. Contradiction, so `ω=0`. ⟹
`Φ` injective ⟹ `g ≤ dim_ℂ H^{0,1}` (= `h1Dim 0` via the comparison).

**This is the *same* positivity `(i/2)∮∮ ω∧ω̄ > 0` that `#7` (`exists_periodLattice_realBasis`) needs**
(Riemann's second bilinear relation) — see `period_lattice_realbasis_research.md`. The integration
engine (cut-surface → planar `4g`-gon → Mathlib divergence theorem / `CurveIntegral` / `extDeriv`) is
shared. So the EASY half is *not new analysis* beyond #7; it is bookkeeping on top of the #7 build.

### 2b. HARD half — `Φ` surjective ⟹ `dim_ℂ H^{0,1} ≤ g` [the wall]

Surjectivity = every `(0,1)`-class has a **conjugate-holomorphic** (= harmonic, on a curve)
representative. Equivalently: the `∂̄`-cokernel `A^{0,1}/im ∂̄` is no bigger than `Ω(X)`. This is the
**existence** half of Hodge/Serre and needs one of:
- **Hodge decomposition** `A^{0,1} = (harmonic) ⊕ im ∂̄` via the `∂̄`-Laplacian + **elliptic
  regularity** + **Fredholm/closed-range**; or
- **Weyl's lemma** + L² methods (Forster §19–§24 route); or
- **residue-pairing perfectness** (Forster §17): the pairing `H¹(𝒪) × Ω(X) → ℂ` is nondegenerate on
  the `H¹` side too — this is where the analysis hides, even though the *pairing* reuses integration.

There is **no cheap shortcut**, and the `g=0` headline case is **not** exempt: it needs `h1Dim 0 = 0`,
i.e. `∂̄ : A⁰ → A^{0,1}` surjective on a genus-0 surface — still global `∂̄`-solvability-with-obstruction
= the same wall. Likewise `cohomological_riemannRoch` (χ-additivity, proven mod skyscraper) gives
`h⁰(D) − h¹(D)` in terms of the **arithmetic** genus `p_a := h¹(0)`; the identity `p_a = g` (geometric)
is *exactly* this bridge — χ-additivity cannot supply it. [VERIFIED by structural analysis]

---

## 3. Mathlib status (this session's survey) [VERIFIED]

**Absent (the whole differential-geometric layer):** differential forms `Ω^k` on manifolds; exterior
derivative `d` on manifolds; de Rham cohomology; Dolbeault cohomology / `∂̄` operator (beyond the plane);
integration of forms over a manifold/chain; manifold Stokes; **Hodge decomposition**; **elliptic
regularity**; Fredholm theory for differential operators; Weyl's lemma; ∂̄-estimates;
Rellich–Kondrachov. (Hodge theory is a known multi-year Lean gap, no open PR.)

**Present & reusable:**
- **Divergence theorem on boxes** `MeasureTheory.Integral.DivergenceTheorem` (2-D Green, countable
  exceptional set) — the engine for the EASY-half positivity (planar, chart-local).
- **`Mathlib.MeasureTheory.Integral.CurveIntegral`** — `curveIntegral`, concat/symm, **homotopy
  invariance of closed-form integrals**; `Convex.exists_forall_hasDerivWithinAt` (primitive on a convex
  set); `Analysis.Complex.HasPrimitives` (Morera). Closes the "primitive on the cut surface" gap.
- **`Analysis.Calculus.DifferentialForm`** — `extDeriv`, `d²=0`, `extDeriv_pullback` (on **normed
  spaces**, not manifolds — fine because the proof is chart-local).
- **Harmonic functions + Laplacian on ℝⁿ** (`Analysis.InnerProductSpace.Harmonic`, `…Laplacian`) —
  building blocks for a harmonic-rep argument, but no operator-on-forms / Hodge wrapper.
- **Hilbert spaces + orthogonal projection** (`InnerProductSpace.Projection`) — the abstract Hodge
  ingredient (projection onto a closed subspace), but the *closed-range* fact for `∂̄` is the missing
  analysis.
- **Sobolev spaces (distributional, Bessel-potential, on ℝⁿ)** `Analysis.Distribution.Sobolev` — recent;
  not yet the Sobolev-embedding/elliptic toolkit a Hodge proof needs.
- Cauchy integral / Cauchy–Goursat in ℂ (`Analysis.Complex.CauchyIntegral`).

**Repo-built and reusable (axiom-clean unless noted):** intrinsic ∂̄ operator `RealForms.dbar`/`dbarL`;
the `(0,1)`-forms `OneFormsZeroOne`/`DolbeaultH01`; the **Dolbeault comparison** `H¹(𝒪)≅H^{0,1}` (RT1 +
crux done this session, RT2 scoped); `finiteDimensional_cechH1` (de-risked, Montel/Riesz); the planar
∂̄-disk solvability `DbarDisk`/`cauchyTransform`; the #7 cut-surface/period/Green machinery (R1/R2 +
`periodVec_linearIndependent` — the positivity infrastructure); `HolomorphicOneForms` finite-dim (Montel).

---

## 4. Routes for the HARD half, ranked

**Route B — Forster residue-pairing perfectness [RECOMMENDED, the repo's chosen route].** Define the
pairing `H¹(𝒪) × Ω(X) → ℂ` (Čech-residue, Forster §17); the integration side reuses #7. Show
nondegeneracy on the `H¹` side using the **finiteness theorem** (done) + Dolbeault + Weyl's lemma. This
is the architecture map's `serre_h1_eq`/`arithmeticGenus_eq_genus` 🔴 box ("residue pairing: ✅ int side;
🔴 perfectness"). Smaller than full Hodge because it leans on the already-built finiteness. Still
research-grade (Weyl's lemma / elliptic regularity for the obstruction-vanishing is the irreducible
core). **Estimate: multi-month; the single genuine wall of the project.**

**Route A — full Hodge-Laplacian decomposition.** Build the `∂̄`-Laplacian, prove elliptic regularity +
closed range + Fredholm, get `A^{0,1} = harmonic ⊕ im∂̄`, identify harmonic `(0,1)` with `Ω̄`. Most
classical, **strictly larger** (needs Sobolev-embedding/elliptic toolkit Mathlib lacks). Not recommended.

**Route C — Weyl's lemma + L² (Hörmander) directly.** Solve `∂̄u=f` in L² with the holomorphic
obstruction; the obstruction space is `Ω(X)`. Comparable to B's core; B is preferable because it slots
into the existing Forster scaffold (finiteness + Čech) the repo already follows.

---

## 5. Cost & strategic read

- **EASY half (`g ≤ h1Dim`):** ~the #7 build (2–4k LoC, partly built). High value: it is *shared* with
  #7 (`exists_periodLattice_realBasis`) and contributes to #1b. A defensible, finite, mostly-scaffolded
  target.
- **HARD half (`h1Dim ≤ g`):** research-grade, multi-month, **no Mathlib scaffolding**. This is the
  irreducible wall and is shared by the RR headline, #1b, and (via RR) #3. Formalizing it = contributing
  Serre duality / a slice of Hodge theory to the ecosystem — a project in its own right.

**Therefore:** full sorry-free `genus_eq_zero_iff_homeo` is gated on a Serre-duality formalization that
is realistically a multi-month-to-year effort with zero upstream support. The **honest, already-reached
milestone** is: *the entire challenge API and the Riemann–Roch ladder are mechanized and axiom-clean
modulo a small, explicit set of named classical-theorem kernels* — `arithmeticGenus_eq_genus`/
`serre_h1_eq` (Serre duality), `deg_div` (residue theorem), `exists_cutSurface` (#7), and
`abelJacobi_twoPoint_ne_zero` (#3). Each is a single TRUE statement, not open design.

---

## 6. Concrete next steps (if pursuing a real discharge)

1. **Finish the Dolbeault comparison (RT2 + wire `cechH1_dolbeault_comparison`).** Needed on *every*
   route; ~1 focused session; the gateway (`holoFn_cocycle_add`) is done. Removes one named kernel.
2. **Build the EASY half** as `genus_le_h1Dim` reusing the #7 cut-surface/Green/positivity engine
   (coordinate with the #7 build — same `(i/2)∮ω∧ω̄>0`). Gives `g ≤ h1Dim 0` axiom-clean.
3. **Isolate the HARD half** as a single named kernel `serre_pairing_perfect`
   (`h1Dim 0 ≤ genus`), documented against Forster §17. Then `arithmeticGenus_eq_genus` = step 2 + step 3
   (antisymmetry of `≤` on `ℕ`), and the project's unproved surface shrinks to that one kernel + residue
   + #3 + #7.
4. Only after 1–3, if the Serre-duality formalization is greenlit as a standalone multi-month effort,
   attack `serre_pairing_perfect` via Route B (Weyl's lemma core).

**My recommendation to the maintainer:** do steps 1–3 (finite, high-value, shrinks and clarifies the
surface), then *decide explicitly* whether to commit to the step-4 Serre-duality build or to declare the
"modulo named classical kernels" milestone as the deliverable. Steps 1–3 are the right work regardless of
that decision.

---

# EXECUTION PLAN — the PDE-free Serre/RR build (fresh session: execute this)

**Goal.** Discharge the Riemann–Roch path sorry-free, establishing `exists_riemannRoch_divisor`
(`RiemannRoch.lean:283`), which the repo already wires to the forward headline
(`exists_singleSimplePole_of_genus_zero` → degree-1 map → `ℂℙ¹ ≃ₜ S²`, all done). The composition
`riemannRoch_equality_of_ladder` (`DolbeaultLadder.lean`, PROVEN) reduces RR to **4 ladder leaves +
`deg_div`**. Per the CORRECTION above, **all of these are PDE-free** (finiteness = functional analysis;
Serre = residues + RR + linear algebra; residue thm = degree route). No Hodge/Weyl/elliptic anywhere on
this path.

## The open sorries on the RR path (the entire surface to discharge)

| Forster | Lean target | file:anchor | status | kind |
|---|---|---|---|---|
| 14.9 finiteness | `finiteDimensional_cechH1` ⟸ `exists_cechModel` | `DolbeaultLadder.lean:44` ⟸ `CechFinitenessWiring.lean:282` | sorry; engine ~95% built (`Montel/*`) | functional analysis (Montel + Schwartz 14.8) |
| 16.x χ-additivity | `cohomological_riemannRoch` ⟸ `exists_skyscraperLES` | `CohomologicalRR.lean:300` | proven **mod** skyscraper sorry | homological algebra (skyscraper SES + snake) |
| 17.3/17.9 Serre @ D=0 | `arithmeticGenus_eq_genus` | `DolbeaultLadder.lean:55` | sorry | **residues + RR + finite-dim linalg (PDE-FREE)** |
| 17.9 Serre general | `serre_h1_eq` | `DolbeaultLadder.lean:62` | sorry | same |
| 4.25 residue thm | `deg_div` ⟸ `exists_properMapDegree` | `RiemannRoch.lean:290` ⟸ `DegDivResidue.lean:213` | sorry; `f.div=0` subcase done | degree route (Rouché + Riemann–Hurwitz count) |
| h⁰=l bridge | `cechRestrictL_surjective` | `CechH0.lean:513` | sorry | Čech gluing/surjectivity |
| RR headline | `exists_riemannRoch_divisor` | `RiemannRoch.lean:283` | sorry; composes the above | bookkeeping (ladder PROVEN) |

## Build order — DE-RISK THE NEVER-BUILT CORE FIRST

### ⏳ BUILD LOG — upstream atoms (2026-06-03, in progress)

**SORRY-FREE LOCAL RESIDUE CALCULUS FOR §17 — COMPLETE (all axiom-clean, depends on NO sorry).**
Constraint honored: nothing below rests on `deg_div`/`finiteDimensional_cechH1`/ladder leaves. Files:
- `Residue.lean` — `resAt` atom (below) + `resAt_add/_smul` (ℂ-linear), `resAt_congr` (germ-invariant),
  `resAt_eq_of_eventuallyEq_sub_inv` (simple-pole reader), `resAt_eq_zero_of_differentiableOn_ball`.
- `SerreDuality.lean` — both abstract finite-dim cores: `finrank_le_of_injective_to_dual` (EASY:
  ι₀ inj ⟹ `genus ≤ h1Dim 0`) + `serre_surjectivity_dim_core` (HARD).
- `FormCoeff.lean` — `coeffAt α a` (analytic chart coefficient, reusing the axiom-clean Montel bridge
  `localRep_analyticOn_chartTarget`); `formFnResidue α g a` = `Res_a(α·g)` + `_eq_zero_of_analyticAt`
  (`Res(holo)=0`); `exists_localRep_self_ne_zero` (`α≠0 ⟹` nonzero coeff somewhere);
  **`exists_formFnResidue_eq_one_of_localRep_ne_zero`** (Forster §17.6 witness: at a nonzero-coeff
  point, `g=1/(z·coeff)` gives `Res_a(α·g)=1`). This is the **local heart of ι₀ injectivity**.

**⛔ SORRY-FREE BOUNDARY REACHED for the EASY half.** Assembling these into the actual map
`ι₀ : H⁰(X,Ω) → (cechH1 0)*` and the inequality `genus ≤ h1Dim 0` requires two things that are
currently sorries, so we stop here rather than depend on them:
  (1) **`Res : H¹(X,Ω) → ℂ`** (Mittag–Leffler) — its *well-definedness on classes* needs the residue
      theorem `∑Res=0` = `deg_div` (degree route, Phase 2 sorry);
  (2) **`FiniteDimensional ℂ (cechH1 𝔘 0)`** = `finiteDimensional_cechH1` (Phase 1 sorry) — needed for
      `finrank_le_of_injective_to_dual` to fire.
The local witness (`Res_a(α·g)=1`) is sorry-free; the *global* `Res` and the finrank step are gated on
(1)/(2). Resuming the EASY half requires discharging `deg_div` and finiteness first (Phases 1–2), OR
stating a **conditional** `genus_le_h1Dim_of_residueTheorem_of_finite` (sorry-free, hypotheses (1)+(2))
— the doc-blessed conditional form. Lesson: `lean_verify`(LSP) can falsely report `sorryAx` when an
imported file changed mid-session; trust `lake build` (no "uses sorry" warning) +
`lake env lean #print axioms`.

LATER lines — original atom log (kept):

Building Phase-0 **from upstream down**. Done so far (`Jacobians/Dolbeault/Residue.lean`, axiom-clean):
- **The residue atom `resAt (f : ℂ → ℂ) (c : ℂ)`** — `(2πi)⁻¹ ∮_{|z-c|=r} f` as `r→0⁺` (`limUnder`,
  mirrors `holoRepr`). Mathlib has **no** residue API (only `meromorphicTrailingCoeffAt` = leading
  coeff), so built on Mathlib's `circleIntegral` + Cauchy–Goursat. Pure 1-var ℂ analysis, no manifold.
- Properties: `resAt_const_mul_sub_inv` (`Res_c(a/(z-c))=a`, Forster 17.6 witness),
  `resAt_eq_zero_of_differentiableOn_ball` (`Res_c(holo)=0`), `circleIntegral_annulus_eq`
  (radius-independence), `resAt_eq_smul_circleIntegral` (compute by any small contour),
  `resAt_add`/`resAt_smul` (ℂ-linearity), `MeromorphicAt.holoPunctured` (Mathlib bridge).

**KEY ARCHITECTURE FINDING (avoids a hard lemma):** the residue of a *function* is chart-dependent, but
Forster's §17.2 cover-independence (`ω_i,ω_j` give the same `Res_a`) needs only `Res(holo)=0` +
additivity — **both proved**. So by always computing `Res_a` in the **canonical chart `chartAt ℂ a`**,
we **never need the heavy "residue-of-a-1-form is chart-independent" change-of-variables lemma** (a
contour-reparametrization proof Mathlib doesn't scaffold). This removes the scariest analytic plumbing
from the route.

**SCOPING DECISION (2026-06-03, user): D=0 only** — target just `arithmeticGenus_eq_genus`
(`h1Dim 0 = genus`), the single Serre leaf the forward headline `genus 0 → S²` needs. Skip packaging
general `serre_h1_eq` and the global `Ω_{-D}≅𝒪_{K-D}` iso (those are for general-`D` RR / `#3` Abel).

**Refined D=0 plan (the equality splits, both halves PDE-free):** `cohomological_riemannRoch` (verified
exact statement `h0Dim D − h1Dim D = deg D + 1 − h1Dim 0`) bakes in `p_a = h1Dim 0` and so gives **no**
shortcut to `p_a = g` — the equality genuinely needs both directions of the §17 residue pairing
`ι₀ : H⁰(X,Ω) → H¹(X,𝒪)*`, `ι₀(ω) = (ξ ↦ Res(ω·ξ))`:
- **EASY half `genus ≤ h1Dim 0`** = `ι₀` *injective* (Forster 17.6). PDE-free and the more tractable
  piece: needs only the residue atom (✅) + the explicit 17.6 witness, built from the **existing**
  `HolomorphicOneForms` (repo) and `MeromorphicFunction` (repo) types — **no global meromorphic-1-form
  type, no `ω₀`-existence**. This is the doc-blessed *weaker, one-directional, genuinely sorry-free*
  deliverable (see the START-HERE constraint) and the right next milestone.
- **HARD half `h1Dim 0 ≤ genus`** = `ι₀` *surjective* (Forster 17.9). Reuses the abstract
  `serre_surjectivity_dim_core` (✅) but its dimension count needs `H⁰(Ω_{nP})` = **global meromorphic
  1-forms with poles ≤ nP**, hence DOES need a meromorphic-1-form representation + **`ω₀`-existence**
  (a nonconstant meromorphic function/form on `X`; comes from finiteness/RR — itself a sub-theorem).
  ⚠ Correction: my first Option-A note wrongly said D=0 avoids `ω₀`; only the EASY half does.

**Shared next module — `Res : H¹(X,Ω) → ℂ`** (needed by both halves), via Mittag–Leffler
distributions, well-defined via `∑Res=0` (= `deg_div`, Phase 2) + the canonical-chart cover-independence
above. Its upstream-most sub-piece: the **coefficient of a holomorphic form `ω` in the canonical chart**
`coeffAt ω a : ℂ → ℂ` (analytic; via `CotangentCoeff.apply_eq_inCoordinates`), so that the local residue
of `ω·f` at `a` is `resAt (coeffAt ω a · (f ∘ chartAt.symm)) (chartAt a a)` — note the appearing
1-forms are all `ω·(meromorphic function)`, so the *holomorphic* `ω` serves as the local reference and
**no abstract meromorphic-1-form type is needed for the EASY half**. Build `coeffAt` next.

### ▶ PHASE 0 (do first — establishes the path, de-risks §17): build Serre duality §17

This is the one piece never attempted and the whole point of "PDE-free." Build Forster §17.1–17.11 to
prove `arithmeticGenus_eq_genus` (and `serre_h1_eq`) **from** `cohomological_riemannRoch` (RR dim
counts) + `finiteDimensional_cechH1` (finiteness) + a residue pairing. These RR/finiteness lemmas are
repo lemmas (currently sorry-backed — that is the inherited structure; Phases 1–2 discharge them). The
**new content is the §17 duality argument**, which is residue calculus + homological algebra + a
finite-dim linear-algebra pigeonhole — verify it formalizes. Sub-steps, following Forster (read PDF
`GTM 81 … Forster ….pdf`, book pp. 132–139 = PDF pp. 138–145):

1. **`Res : H¹(X,Ω) → ℂ`** via local residues / Mittag–Leffler (Forster 17.1–17.2). Define `Res(μ) =
   ∑_a Res_a(μ)` for an M–L distribution of 1-forms (sum of local Laurent residues). Reuse
   `CotangentCoeff.lean` (form-in-coordinates) + the repo residue infra. **Well-definedness on classes
   needs the residue theorem `∑Res = 0`** (Phase 2 / `deg_div`) — so either thread it as a hypothesis
   now and discharge in Phase 2, or do `deg_div` first. (Avoid Forster's 17.3 `∬_X d(·)=0` Stokes
   identity — the Čech-residue route does NOT need manifold 2-form integration.)
2. **Pairing `⟨ω,ξ⟩ = Res(ωξ)`** and `ι_D : H⁰(Ω_{-D}) → H¹(𝒪_D)*` (17.5). `Ω_{-D} ≅ 𝒪_{K-D}` (17.4).
3. **`ι_D` injective** (17.6): explicit M–L distribution `ωη = (dz/z,0)` with `Res = 1`. Residue algebra.
4. **functoriality** (17.7/17.8): cohomology exact-sequence duals + the multiplication-by-ψ diagram.
5. **`ι_D` surjective** (17.9 — THE crux, and it is *pure finite-dim linear algebra*): with
   `D_n = D − nP`, `dim Λ + dim Im(ι_{D_n}) > dim H¹(𝒪_{D_n})*` for large `n` (RR dim counts via
   Lemmas 17.4, 17.8) forces `Λ ∩ Im ≠ ∅`. No analysis — just `Riemann–Roch` inequalities + a
   pigeonhole. **This was the formalizability litmus test for the whole route — ✅ PASSED 2026-06-03**
   (`SerreDuality.serre_surjectivity_dim_core`, axiom-clean). The abstract count is *done*; this sub-step
   now reduces to **instantiating** that lemma with the concrete cohomology objects/maps built in 1–4
   (supply `Λ n`, `I n = Im ι_{D_n}`, and discharge the three RR-bound hypotheses `hΛ/hI/hV` from the
   repo's RR dim counts).
6. **Conclude** `H⁰(X,Ω_{-D}) ≅ H¹(X,𝒪_D)*` (17.11); at `D=0`: `g = dim H¹(X,𝒪)` =
   `arithmeticGenus_eq_genus`; general `D` ⟹ `serre_h1_eq`. Wire into `DolbeaultLadder.lean`.

Estimate ~1000–2000 LoC. Reuse: `CotangentCoeff`, `LineIntegral`, `CechComplex`/`CechSection`,
`RiemannRoch`/`DolbeaultLadder`/`CohomologicalRR`. Mathlib: `Module.Dual`, `Submodule.dualPairing`,
finite-dim linear algebra. **If §17.9 formalizes cleanly, the PDE-free route is established.**

### ▶ PHASE 1: finish finiteness (Forster 14.9) — functional analysis

Discharge `exists_cechModel` (`CechFinitenessWiring.lean:282`) and the Schwartz finiteness lemma
(Forster 14.8). The engine is ~95% reuse — see `docs/cech_finiteness_research.md` (the authoritative
build plan for this node). Reuse `Montel/Cover.lean` (nested triple cover), `Montel/Compactness.lean`
(disk-Montel, Arzelà–Ascoli), `Montel.lean`/`HolomorphicForms.lean` (sup-norm+bcf+Riesz), `DbarDisk.lean`
(Leray vanishing `H¹(disk,𝒪)=0`). Mathlib: `IsCompactOperator` API, `riesz_lemma`,
`FredholmAlternative`, `FiniteDimensional.of_isCompact_closedBall₀`, Banach open-mapping
(`Analysis/Normed/Operator/Banach.lean`). The one genuinely-new FA lemma: Schwartz 14.8 (surjective +
compact perturbation ⟹ finite-codim image), ~100–300 LoC. **No PDE.**

### ▶ PHASE 2: the remaining homological / residue inputs

- **`exists_skyscraperLES`** (`CohomologicalRR.lean:300`): skyscraper SES connecting map + `skyDim=1`
  + snake lemma ⟹ `cohomological_riemannRoch` sorry-free. Homological algebra. (Soundness already
  fixed once — see `[[project_ladder_soundness_audit]]`; the middle term is a genuine 1-dim `ℂ_P`.)
- **`deg_div` / `exists_properMapDegree`** (`RiemannRoch.lean:290` / `DegDivResidue.lean:213`): the
  residue theorem via the **degree route** (`#zeros = deg = #poles` for `f:X→ℂℙ¹`); needs Rouché +
  ramified-degree count (Riemann–Hurwitz). The `f.div=0` subcase is done. PDE-free; see
  `[[reference_abel_riemannroch_path]]` and `DegDivResidue.lean` header. Also unblocks Phase-0 Res
  well-definedness.
- **`cechRestrictL_surjective`** (`CechH0.lean:513`): the `h⁰(𝔘,𝒪_D)=l(D)` bridge's gluing/surjectivity
  (rigidified normal-form; see `[[project_cech_germ_representation]]`).

After Phases 0–2: the RR ladder is sorry-free ⟹ `exists_riemannRoch_divisor` ⟹ forward headline
(`genus 0 → S²`).

## The BACKWARD headline (`homeo S² → genus 0`) — separate, also PDE-free

`genus_zero_of_nonempty_homeo_sphere` (`DegreeOneSphere.lean:675`). **Do NOT route through `g = ½b₁`
(that needs Forster §19 harmonic forms = elliptic).** Instead: a nonzero holomorphic 1-form `ω` is
**closed** (`dω=0`) but **not exact** (`ω=df` globally ⟹ `f` holomorphic on compact `X` ⟹ `f` const ⟹
`ω=0`); a closed-not-exact form ⟹ some loop has `∮_γ ω ≠ 0` ⟹ `X` not simply connected ⟹ not `≃ₜ S²`
(`S²` simply connected). Reuse: Mathlib homotopy-invariance of closed-form integrals
(`MeasureTheory.Integral.CurveIntegral`, `Convex.exists_forall_hasDerivWithinAt`), the repo's
period/primitive machinery (`SmoothPath*`, `PeriodLattice`), max-modulus (`Geometry/Manifold/Complex`),
and `S²` simple-connectivity. **PDE-free.** (Verify this route formalizes; it is the cheap alternative
to topological-invariance-of-genus.)

## Read-first for the fresh session
- **memory:** `[[reference_hodge_bridge_path]]` (this finding), `[[project_sorry_free_roadmap]]`,
  `[[project_ladder_soundness_audit]]` (FALSE-as-stated leaf warnings — re-check statements before
  trusting!), `[[reference_abel_riemannroch_path]]`, `[[project_finiteness_node]]`,
  `[[project_cech_to_dolbeault_progress]]` (RT2, deferred), `[[feature_verify_agent_commits]]`.
- **docs:** this file, `architecture_map.md`, `STATUS.md`, `cech_finiteness_research.md` (Phase-1 plan),
  `archive/riemann_roch_proof_plan.md` (deep RR reference).
- **Forster GTM81 PDF** (repo root): §14 finiteness, §16 RR, **§17 Serre (the Phase-0 source)**,
  §18 Mittag–Leffler. §19 (harmonic) is NOT on this path.

## Discipline (carry over)
Build one module at a time; `lake build <module>` then `#print axioms <name>` (clean =
`[propext, Classical.choice, Quot.sound]`). Commit each verified step. The heavy comparison files
(`DolbeaultComparison*Equiv/Proof`) are slow (~260s) and LSP-unloadable; Phase-0 should live in lighter
files where possible. **Verify every leaf statement against Forster before proving** — the ladder has had
FALSE-as-stated leaves (`[[project_ladder_soundness_audit]]`); a stronger-than-book statement is a
misformalization smell.
