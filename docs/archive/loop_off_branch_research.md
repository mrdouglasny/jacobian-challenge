# Research: discharging sorry #6 `exists_loop_off_branchLocus`

> ✅ **#6 DISCHARGED 2026-06-01 — THIS DOC IS SUPERSEDED.** `exists_loop_off_branchLocus` is
> proven sorry-free + axiom-clean — NOT via the manifold de-Rham / Stokes route explored here, but
> via a standard breakpoint-perturbation + within-ball telescoping (the crux this doc isolated was
> later found *misformalized* and replaced). Retained as a record of the approaches considered.
> Current state: `docs/STATUS.md`; memory `project_loop6_crux_misformalization` (RESOLVED).


READ-ONLY research, 2026-05-31. Repo `/home/rado/jacobian`, Mathlib pin
`8e3c989` / Lean `v4.30.0-rc1`. No tracked files edited.

Legend: **[VERIFIED]** = checked this session (file read, grep, or `lean_run_code`
compile). **[believed]** = standard math / inferred from docstrings, not re-derived.

---

## BOTTOM LINE

- **#6 is NOT a cheap independent win. It is a second big build — the manifold
  Stokes / homotopy-invariance-of-line-integrals nugget — and it is genuinely
  blocked on missing Mathlib math.** It is correctly deferred.
- **#6 IS independent of the Dolbeault/Hodge `∂̄` wall** (#1/#3/#7). It needs a
  *different, strictly weaker* analytic tool (manifold Stokes on a homotopy
  cylinder / homotopy-invariance of `∮ ω` for a closed 1-form), not Serre
  duality / `dim H¹(X,O)=g`. So building #6 would NOT advance #1/#3/#7, and vice
  versa. **[VERIFIED]** the repo's own plan docs say exactly this
  (`docs/abel_riemannroch_research.md:25`; `docs/riemann_roch_proof_plan.md` ties
  the wall only to `dim H¹`, never to #6).
- **Two sub-parts, and the split is decisive:**
  - **(a) Existence of an off-branch loop — CHEAP / ~DONE-ABLE NOW (~150–250 LoC).**
    The repo already proves the hard topological input:
    `isPathConnected_compl_finite_of_connected_chartedSpace_complex`
    (`Jacobians/Discharge/Manifold/PathConnectedComplFinite.lean:236`,
    `theorem`-level, in-repo) **[VERIFIED present]**. Branch locus finite
    (`finite_branchLocus_of_nonconstant` **[VERIFIED used]**). This sub-part needs
    no missing math.
  - **(b) Period-PRESERVATION `periodVec δ' = periodVec δ` — the CRUX, and it
    needs manifold Stokes that Mathlib LACKS.** The consumers require the new loop
    to have the *literally equal* period vector (it is threaded through
    `PreimageCycle.congr_periodVec`, which `rw`s a `periodVec δ = periodVec δ'`
    equality). Getting that equality from "δ' is homotopic to δ" is precisely the
    homotopy-invariance of the line integral of a closed holomorphic 1-form =
    Stokes on the homotopy cylinder. **[VERIFIED]** the repo states this in prose
    (`Jacobians/PeriodLattice.lean:1567–1576`) deliberately, to avoid an unsound
    placeholder, and folds it into #6.
- **LoC estimate to actually discharge #6 honestly: ~1.5k–3k LoC** (a manifold
  Green/Stokes-on-a-square layer), comparable to the #7 cut-surface build, and
  resting on the *same family* of "subdivide-into-chart-boxes + 2D Green" tools
  the #7 work is using — but here over a homotopy cylinder `[0,1]²`. It is a
  **build**, not a search-for-the-right-lemma. **[believed]**, calibrated against
  `docs/period_lattice_realbasis_research.md` (~2–4k for the analogous #7 Green
  layer).
- **Mathlib HAS** a Poincaré/curve-integral homotopy-invariance theorem
  (`ContinuousMap.Homotopy.curveIntegral_add_curveIntegral_eq_of_diffContOnCl`
  and siblings) **[VERIFIED compiles]** — but **only for normed spaces `E`**,
  with the form as `ω : E → E →L[𝕜] F`, a `C²` homotopy, and a *closed* form
  (symmetric Fréchet derivative). It is **NOT** a manifold theorem and does **NOT**
  apply to the repo's `lineIntegral : HolomorphicOneForms X → (ℝ→X) → ℂ` on a
  surface, except inside a single chart. Bridging it to the manifold is the build.

**Recommendation: keep #6 deferred** alongside #7 / the Hodge work; it is not a
do-now. If any partial progress is wanted, sub-part (a) (the off-branch loop's
*existence*, ignoring period) is a clean, self-contained, math-complete lemma that
could be split out — but it does not on its own discharge #6, because #6's
signature demands the period equality, which is (b).

---

## 1. Exact statement + role

`Jacobians/TracePullback.lean:344` **[VERIFIED]**:

```lean
theorem exists_loop_off_branchLocus (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀)
    (δ : ℝ → Y) (hδ : IsClosedSmoothLoop δ) :
    ∃ δ', IsClosedSmoothLoop δ' ∧ periodVec δ' = periodVec δ ∧
      (∀ t : ℝ, δ' t ∉ branchLocus f) :=
  sorry
```

- `IsClosedSmoothLoop` (`Jacobians/SmoothPathCore.lean:109`) **[VERIFIED]**:
  `closed : γ 0 = γ 1`, `cont`, chart-pullback `diff` on `uIcc 0 1`, and `velCont`
  (tangent-section continuity on `Icc 0 1`). From `velCont` the per-basis-form
  integrand is interval-integrable (`.integrable`).
- `periodVec γ i = lineIntegral (periodBasisForm X i) γ`
  (`SmoothPathCore.lean:101`), `lineIntegral α γ = ∫ t in 0..1, α(γ t)(pathSpeed γ t)`
  (`Jacobians/LineIntegral.lean:61`), `pathSpeed` via the chart around `γ t`
  (`LineIntegral.lean:54`). **[VERIFIED]**
- `branchLocus f = f '' criticalSet f`, `criticalSet f =
  Discharge.Manifold.criticalSetGeneral f` (not-locally-injective set)
  (`Jacobians/PeriodLattice.lean:996,1000`). Finite for non-constant `f`:
  `finite_branchLocus_of_nonconstant`. **[VERIFIED]**

**Cleanest mathematical claim.** *Every closed smooth loop `δ` on the surface `Y`
is homologous (here it suffices: homotopic rel basepoint, then perturbed) to a
closed smooth loop `δ'` that misses the finite branch locus and has the same period
vector `∮_{δ'} ωᵢ = ∮_δ ωᵢ` for every holomorphic basis 1-form `ωᵢ`.* Because the
branch locus is finite (real codimension 2 in the real surface), a generic small
perturbation already avoids it; period equality is homotopy-invariance of `∮ ω` for
a *closed* form. **[believed]** (Forster §10.5.)

**How `pushforward_pullback` consumes it.** Critical-path leaf, used at exactly two
sites **[VERIFIED]**, both inside the preimage-cycle machinery:

- `exists_preimageCycle_of_nonconstant` (`TracePullback.lean:1778`): obtains
  `⟨δ', hδ', hpv, havoid⟩`, lifts `δ'` to a `PreimageCycle f hf δ'` via
  `exists_preimageCycle_of_off_branchLocus` (which is PROVEN and requires
  `havoid : ∀ t, δ' t ∉ branchLocus f`), then transports back to a
  `PreimageCycle f hf δ` along `hpv : periodVec δ' = periodVec δ` via
  `PreimageCycle.congr_periodVec` (`TracePullback.lean:1764`).
- `exists_preimageCycle_sheets_eq_fibreCard_of_nonconstant`
  (`TracePullback.lean:1828`): identical pattern, also tracking `sheets = #fibre`.

These feed `ambientPullbackJac_periodVec_mem_truePeriodLattice` →
`ambientPullbackJac_preserves_truePeriodLattice` → the ZLattice quotient →
`Jacobian.pushforward_pullback`. **[VERIFIED]** chain by grep.

`PreimageCycle.congr_periodVec` is literally:
```lean
pullback_eq := by rw [h]; exact c.pullback_eq   -- h : periodVec δ = periodVec δ'
```
i.e. it needs the *equality of period vectors*, not "homotopic". **This is why the
period-preservation conjunct (b) is load-bearing and cannot be dropped.**
**[VERIFIED]**

---

## 2. Classical proof and the two sub-parts

Standard argument (Forster §10): branch locus `B = branchLocus f` is a finite set
of points on the surface `Y`. (a) Perturb/homotope the loop `δ` off `B`
(genericity: a generic loop in a real-2-manifold misses finitely many points, since
points have codim 2). (b) Periods are homotopy-invariant: `∮ ω` of a *closed*
holomorphic 1-form is unchanged under a homotopy of loops, by Stokes on the homotopy
cylinder `H : [0,1]² → Y`, since `∮_{δ'} ω − ∮_δ ω = ∬_{[0,1]²} H^*(dω) = 0`
(`dω = 0`; holomorphic 1-forms are closed). **[believed]**

### (a) Existence of the off-branch homotopy — topology/genericity. NOT the crux.
**The repo already proves the heavy input.**
`isPathConnected_compl_finite_of_connected_chartedSpace_complex`
(`PathConnectedComplFinite.lean:236`) **[VERIFIED present]**:
```lean
theorem … {C : Set Y} (hC_fin : C.Finite) (hC_compl : (Cᶜ : Set Y).Nonempty) :
    IsPathConnected (Cᶜ : Set Y)
```
With `C = branchLocus f` (finite, **[VERIFIED]**) this hands you a path-connected
`Yᶜ`. The remaining work for (a) is to turn "the loop's points can be pushed into
`Bᶜ`" into an actual *closed smooth loop* with `velCont`/`diff`/integrability — the
same chart-ball-hop + concat toolkit the repo already has
(`exists_zeroVel_smoothPath`, `IsSmoothPath.concat`, `flatEndReparam`). This is
genuine engineering (~150–250 LoC) but **needs no missing math**. **[believed]**

NB: Mathlib has **no** Sard / transversality / "perturb a path off a finite set"
genericity API — **[VERIFIED]** (`Mathlib/Topology/Homotopy/*` is purely
topological; no differential genericity; the grep hits for "Sard/transversal" were
false positives in group theory). So sub-part (a), if done, is done via the repo's
already-built path-connected-complement route, not via a Mathlib genericity lemma.

### (b) Period-preservation under the homotopy — Stokes/de Rham. THE CRUX.
To conclude `periodVec δ' = periodVec δ` you need: *homotopic closed smooth loops
have equal `lineIntegral` of any holomorphic (closed) 1-form*. This is **manifold
Stokes on `[0,1]²`** (equivalently homotopy-invariance of de Rham periods). The repo
states it only in prose, deliberately, to avoid an unsound placeholder
(`PeriodLattice.lean:1567–1576`) **[VERIFIED]**:

> *`periodVec` is homotopy-invariant … because the period forms are closed
> holomorphic 1-forms and `∫_γ ω` depends only on the homotopy class by Stokes on
> the homotopy cylinder (Forster §10.5; **Mathlib lacks manifold Stokes**).*

**This sub-part is the entire difficulty of #6.** It is what makes #6 a build, not a
search.

---

## 3. Does #6 need the Dolbeault/Hodge wall? NO — independent.

- **The Dolbeault wall** (for #1/#3/#7) is `∂̄`-solvability ⇒ `dim H¹(X,O)=g` /
  Serre duality. **[VERIFIED]** every mention in `docs/riemann_roch_proof_plan.md`
  ties the wall to `dim H¹`, finiteness, Serre's residue pairing — never to #6.
- **#6 needs only**: (i) finite-set-avoidance (topology, repo has it) + (ii)
  homotopy-invariance of `∮(closed 1-form)` = manifold Stokes on a square. Stokes is
  **strictly weaker** than Dolbeault (Stokes is `∫dω = ∫∂ ω`, a calculus identity;
  Dolbeault is an elliptic-PDE solvability theorem). They share no engine.
- **Consequence**: building #6 would NOT discharge any of #1/#3/#7, and the #7
  cut-surface/Green work does NOT discharge #6 (the #7 Green is on a *planar 4g-gon*
  for the bilinear relations; #6 needs Stokes on the *homotopy cylinder of a loop in
  the surface*, glued chart-to-chart along the cylinder). They are *adjacent*
  (both want a manifold-Stokes-flavored tool) but not the same theorem.
  **[believed]**, consistent with `docs/abel_riemannroch_research.md:25,30`.

So: #6 is **independent of the big wall**, but it is **its own wall** (a smaller,
Stokes-shaped one).

---

## 4. Mathlib inventory (verified names)

### PRESENT and relevant

- **Homotopy-invariance of curve integrals of CLOSED 1-forms (normed-space only).**
  `Mathlib/MeasureTheory/Integral/CurveIntegral/Poincare.lean` **[VERIFIED compiles]**:
  - `ContinuousMap.Homotopy.curveIntegral_add_curveIntegral_eq_of_diffContOnCl`
  - `…curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt`
  - `…curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt_off_countable`
  - plus `Convex.*` Poincaré-primitive lemmas
    (`curveIntegral_segment_add_eq_of_hasFDerivWithinAt_symmetric`,
    `exists_forall_hasDerivWithinAt`, …).
  Signature **[VERIFIED]**: `E` a `NormedSpace`, `ω : E → E →L[𝕜] F`, needs a `C²`
  homotopy `φ : (↑γ₁).Homotopy ↑γ₂`, "closed" encoded as symmetry of the (within-)
  Fréchet derivative `dω x u v = dω x v u`. **Conclusion form** is the *boundary-of-
  square* identity `∫γ₁ + ∫(φ.evalAt 1) = ∫γ₂ + ∫(φ.evalAt 0)` (the four sides of
  `[0,1]²`); for a loop homotopy with degenerate vertical sides this gives equality
  of the two horizontal integrals.
  **Gap to this repo**: this is `curveIntegral` (normed-space, `Path a b`, `ω :
  E→E→L F`), NOT `Jacobians.lineIntegral` (manifold, `HolomorphicOneForms X`,
  `pathSpeed` via charts). Usable only *inside one chart*. **[VERIFIED]** the def
  `curveIntegral` carries `[NormedSpace 𝕜 E]`.

- **`curveIntegral` / `curveIntegralFun`** basic API
  (`CurveIntegral/Basic.lean`): notation `∫ᶜ x in γ, ω x`, linearity, segment
  derivative. Normed-space. **[VERIFIED present]**

- **Covering-map path lifting + monodromy** (the repo already imports & uses these):
  `IsCoveringMap.liftPath`, `…liftPath_lifts`, `…liftPath_zero`, and
  `IsCoveringMap.liftPath_apply_one_eq_of_homotopicRel` **[VERIFIED compiles]**:
  ```lean
  cov.liftPath_apply_one_eq_of_homotopicRel :
    γ₀.HomotopicRel γ₁ {0,1} → … → (cov.liftPath γ₀ e h₀) 1 = (cov.liftPath γ₁ e h₁) 1
  ```
  (`Mathlib/Topology/Homotopy/Lifting.lean`). This is monodromy of *lift endpoints*
  from homotopy of the *base* loop — useful for the #3 lift geometry (already in
  use), **but it does NOT give period equality of δ' vs δ** (it is about lifts in
  `X`, not the integral `∮_{δ'}ω` in `Y`).

- **Path homotopy API**: `Path.Homotopy`, `ContinuousMap.Homotopy`,
  `Path.Homotopic`, `…HomotopicRel`, `ContinuousMap.Homotopy.affine`
  (`Topology/Homotopy/{Basic,Path,Affine,Lifting}.lean`) **[VERIFIED files present]**.
  Purely topological / `C⁰`.

- **Path-connected complement of a finite/countable set in the surface** — provided
  IN-REPO by `isPathConnected_compl_finite_of_connected_chartedSpace_complex`
  (built on `Set.Countable.isPathConnected_ball_diff_complex`, ZZ164b). **[VERIFIED]**
  The Mathlib primitive the repo leans on for the ball case lives under
  `Jacobians/Discharge/Manifold/IsPathConnectedBallMinusCountable.lean`.

- **2D divergence / Green** (the actual Stokes-grade tool, normed/box form):
  `MeasureTheory/Integral/DivergenceTheorem.lean`,
  `Analysis/BoxIntegral/DivergenceTheorem.lean`
  (`integral_divergence_of_hasFDerivWithinAt_off_countable`, the 2D Green
  corollary). **[VERIFIED files present]** — this is what `Poincare.lean` itself is
  built on, and what a manifold-Stokes-on-a-square layer would also build on.

### ABSENT (honest absent-list) — all **[VERIFIED]** by grep over the pinned Mathlib

- **Manifold Stokes** `∫_M dω = ∫_∂M ω`: absent. No `Stokes`/`stokes` anywhere in
  `Mathlib/Geometry/`.
- **Manifold de Rham cohomology / `extDeriv` on manifolds / integration of
  differential forms over manifolds**: absent. `Mathlib/Geometry/Manifold/` has
  `IntegralCurve/*`, `MFDeriv`, bundles — but **no form-integration, no de Rham, no
  exterior derivative on manifolds**. (The user confirmed this directly.)
- **Homotopy-invariance of de Rham/line-integral periods ON A MANIFOLD**: absent.
- **Smooth / `ContMDiff` homotopy of maps between manifolds**: absent —
  `Mathlib/Topology/Homotopy/*` is `C⁰` only; no `ContMDiffHomotopy`. This matters:
  even to *invoke* a manifold Stokes you'd first need a *smooth* homotopy of loops,
  which Mathlib can't even state.
- **Sard's theorem / transversality / differential genericity / "perturb a path off
  a finite set"**: absent.
- **`Mathlib.MeasureTheory.Integral.CurveIntegral` as a single file** — note the
  brief's name is slightly off: it is a **directory** with `Basic.lean` +
  `Poincare.lean`. **[VERIFIED]**

---

## 5. Prior art: evaristebernhard/Stokes

**Not usable as a drop-in, and not a clean bridge.** **[VERIFIED]** against the repo
memory `reference_stokes_repo.md`:

- It proves equality of **"coordinate-represented" endpoints** (canonical finite
  coordinate sums internal to its proof route), **not** Mathlib's `∫_M dω = ∫_∂M ω`
  and **not** the repo's real `lineIntegral`. Its bridge to real integration
  *explicitly leaves the geometric work (carrier selection, boundary orientation,
  the global boundary integral) as input hypotheses*. Oriented-manifold integration
  + induced boundary orientation + de Rham are on its **roadmap, not done**.
- **No LICENSE** (legal blocker; author was being contacted 2026-05-30).
- Version gap (its v4.29.1 vs repo v4.30.0-rc1) and its own `ManifoldForm`/
  represented-integral types vs the repo's `HolomorphicOneForms` + `lineIntegral`.

It is a *reference for the shape* of a manifold-Stokes argument, **not** a port that
shortcuts (b). For #6 specifically (homotopy cylinder, not closed-manifold Stokes),
it is even further off. **Decision already on record: leave Stokes-dependent pieces
for last; revisit if it gets a license + a real-integral/de Rham layer.**

---

## 6. Keystone decomposition + LoC + risk

If one were to discharge #6 honestly (NOT recommended now), the build is a
**manifold-Stokes-on-a-square / homotopy-invariance** layer. Keystones:

| # | Keystone | What | LoC | Risk |
|---|----------|------|-----|------|
| K1 | **Off-branch loop existence (sub-part a)** | From `isPathConnected_compl_finite_of_connected_chartedSpace_complex` (repo) + chart-ball-hop/`concat`/`flatEndReparam` toolkit, build a *closed smooth loop* `δ'` (with `velCont`) whose image avoids `branchLocus f`, homotopic to `δ`. | ~150–250 | **Low** — no missing math; pure repo-style assembly. Can be split out & finished independently. |
| K2 | **Smooth homotopy of loops** `δ ⇒ δ'` | A `ContMDiff`/chart-pullback-`C²` homotopy `H : [0,1]² → Y` rel basepoint, with `H` landing chartwise. Mathlib has only `C⁰` homotopy, so this is from scratch (state + construct via the same chart-ball cover). | ~300–500 | **Med** — fiddly but no deep theorem; needed even to *state* Stokes. |
| K3 | **Chart-localized Green/Stokes on `[0,1]²`** | Pull `ωᵢ` back along `H` into each chart; on the part of `[0,1]²` mapping into one chart, apply Mathlib's normed-space Poincaré (`curveIntegral_add_curveIntegral_eq_of_diffContOnCl`) / 2D divergence theorem to get the box identity. | ~400–700 | **Med-High** — the integrand is `ωᵢ(H)(∂H)`; matching `lineIntegral` (manifold, `pathSpeed`-via-chart) to `curveIntegral` (normed) is real glue, incl. the ℝ/ℂ `restrictScalars` diamond the repo already fights. |
| K4 | **Subdivide-and-patch the cylinder** | Cover `[0,1]²` by finitely many sub-rectangles each mapping into a single chart (Lebesgue number, as in `exists_nbhd_cover`); sum K3 over the grid; interior chart-seams cancel; only the two horizontal sides (`δ`, `δ'`) survive ⟹ `∮_δ ωᵢ = ∮_{δ'} ωᵢ`. | ~400–800 | **High** — the seam-cancellation bookkeeping is the heart of "manifold Stokes" and is where the evaristebernhard repo also stops short. |
| K5 | **Assemble `exists_loop_off_branchLocus`** | `periodVec δ' = periodVec δ` (componentwise K4) + `IsClosedSmoothLoop δ'` (K1) + `havoid` (K1). | ~50–100 | Low, once K1–K4 land. |

**Total: ~1.3k–2.4k LoC**, dominated by K3+K4 (the genuine Stokes content).
**[believed]**, calibrated to `docs/period_lattice_realbasis_research.md`'s ~2–4k
for the structurally-similar #7 Green layer (which the user is actively building).

**What must stay isolated.** Nothing *new* needs an axiom — this is a from-scratch
*proof*, not an assumption. But if a faster path is wanted, the honest isolation is
to **take the homotopy-invariance of `periodVec` as an explicit hypothesis/structure
field** (repo-style, like `PreimageCycle` / `CanonicalDissection` bundle their
classical content) rather than `sorry` — i.e. promote (b) to a named input. That is
an architecture choice (the README's "assume-and-derive", previously declined to
keep the unproved surface visible). **K1 (sub-part a) does NOT need isolation** and
is a clean win on its own.

**Risk ranking vs the Dolbeault wall.**
- **Difficulty**: #6 (K2–K4 manifold-Stokes-on-a-square) is **somewhat easier than
  full Dolbeault** (Stokes is a calculus/measure identity; Dolbeault is elliptic
  PDE) but is **the same order of magnitude of build** (1–2.5k LoC) and shares the
  "subdivide-into-chart-boxes + 2D divergence + seam-cancellation" pattern with the
  #7 Green work. **It is decidedly NOT a do-now cheap win.**
- **Independence**: #6 is **independent** of the wall — building it advances neither
  #1/#3/#7 nor is advanced by them. **[VERIFIED]** from the plan docs.
- **Strategic read**: the cheapest *real* progress on #6 is **K1 only** (off-branch
  loop existence, ignoring period) — a clean, math-complete, ~150–250 LoC lemma that
  could be landed and that documents the boundary precisely; but it leaves the #6
  *signature* unproved because the period-equality (b) is the part Mathlib can't yet
  support. **Keep #6 deferred with #7/Hodge.**

---

## Appendix — session-verified facts

- `exists_loop_off_branchLocus` statement & both consumer sites (1782, 1834) via
  `congr_periodVec`. **[VERIFIED]** (read `TracePullback.lean`).
- `IsClosedSmoothLoop` / `periodVec` / `lineIntegral` / `pathSpeed` definitions.
  **[VERIFIED]**
- `branchLocus`/`criticalSet` definitions; `finite_branchLocus_of_nonconstant`,
  `fiber_finite_off_branchLocus`. **[VERIFIED]**
- `isPathConnected_compl_finite_of_connected_chartedSpace_complex` exists, `theorem`,
  in-repo. **[VERIFIED]**
- Mathlib `Poincare.lean` curve-integral homotopy theorems compile and are
  **normed-space-only** (`[NormedSpace 𝕜 E]`, `ω : E → E →L[𝕜] F`, `C²` homotopy,
  symmetric-derivative "closed"). **[VERIFIED via lean_run_code]**
- `IsCoveringMap.liftPath_apply_one_eq_of_homotopicRel` compiles. **[VERIFIED]**
- Mathlib has **no** manifold Stokes, de Rham, manifold form-integration, manifold
  `ContMDiff` homotopy, or Sard/transversality (grep). **[VERIFIED]** + user-confirmed.
- `Mathlib.…CurveIntegral` is a directory (`Basic.lean`+`Poincare.lean`), not a
  single file. **[VERIFIED]**
- evaristebernhard/Stokes: represented-not-real integrals, no license, roadmap-only
  de Rham. **[VERIFIED via repo memory]** (not re-cloned this session).
