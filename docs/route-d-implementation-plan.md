# Route D — implementation plan (anti-invariance → L2)

*Authored 2026-06-02 (Claude). Decomposed, Codex-sized tasks for the validated
route D (`docs/anti-invariance-route-decision.md`). Branch: `route-d`.*

**Codex usage rule (learned the hard way):** Codex twice failed on this thread —
once thrashing without writing, once **OOM from reading too many large files**.
So every Codex task below ships an **explicit, short reading list** (≤ ~4 files,
named line ranges where possible) and **one** narrowly-scoped deliverable. Never
say "read the repo"; name the files.

## Goal & structure

Prove **(AI)** `ω.coeff(σq, z) = −ω.coeff(q, z)` on smooth-Y projX charts for an
arbitrary `ω : HolomorphicOneForm (HyperellipticEvenProj H)`, then L2. Phases:

- **P0 (design)** — the *transported projX coefficient* `cX ω a`, sidestepping
  `Quotient.out`. **Architectural; do first; owned by Claude/MRD, not Codex.**
- **P1** — branch-point removability of the symmetric scalar `s` (uses the landed
  `OddPartDslope` helper + the existing transition-derivative lemmas).
- **P2** — ∞ growth `s = O(1/x²)`.
- **P3** — global `s`, entire, Liouville ⇒ `s ≡ 0` ⇒ (AI).
- **P4** — L2 from (AI): `g = cX·√f` single-valued, entire, poly-growth ⇒ polynomial.

## Landed already (branch `route-d`)

- `Jacobians/GeneralResults/OddPartDslope.lean` (`1dcb200`):
  `analyticAt_dslope_oddPart` — for `h` analytic at 0,
  `dslope(w ↦ h w − h(−w)) 0` is analytic at 0; `dslope_oddPart_of_ne`. This is
  the Q2 cancellation core (`h(√f) − h(−√f) = √f · dslope(oddPart)(√f)`).

## Reusable infrastructure (already proven in repo — DO NOT rebuild)

- **Chart-transition derivatives** (`AffineForm.lean`):
  `affineChartProjX_to_projY_transition_hasDerivAt:510`,
  `affineChartProjY_to_projX_transition_hasDerivAt:576`,
  `squareLocalHomeomorph_symm_hasDerivAt:472`,
  `squareLocalHomeomorph_symm_eval_analyticOn:211`,
  `squareLocalHomeomorph_symm_ne_zero:78`.
- **Maximal-atlas membership of the affine chart** (proven for Mσ.2,
  `Involution.lean`): `affineLiftChart_mem_maximalAtlas`,
  `infinityLiftChart_mem_maximalAtlas` — the handle for transporting coeff into
  `affineLiftChart a` regardless of `Quotient.out`.
- **σ as a smooth point map** (`Involution.lean`, `3890d91`):
  `hyperellipticEvenInvol`, `…_mk` (`σ⟦inl a⟧ = ⟦inl a.invol⟧`),
  `…_contMDiff`, `HyperellipticAffine.invol_mem_smoothLocusY`.
- **Liouville / growth** (`GeneralResults/EntireGrowth.lean`):
  `differentiable_eq_polynomial_of_growth`; removable singularity:
  `Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`.
- **Form coeff API** (`RiemannSurface/OneForm.lean`): `HolomorphicOneForm.coeff`,
  the three submodule predicates, `ext_of_coeff`. The L3 bridge pattern:
  `Form.lean:297 hyperellipticForm_coeff_projX` (how coeff at a smooth-Y point is
  accessed via `Quotient.out q = Sum.inl a`).

## P0 — the local `dx`-coefficient (DESIGN — do first, Claude/MRD)

> **CORRECTION (2026-06-02), critical — read before coding.** The "transport
> `ω.coeff ⟦inl a⟧` to the **full** affine projX target" framing is **wrong**: it
> hits the **exact §2 crux of `anti-invariance-route-decision.md`** — the
> preferred chart at `⟦inl a⟧` (`Quotient.out`, arbitrary) need not cover the
> whole affine target, so the transport is junk/non-analytic on part of it. Do
> **NOT** build a global `cX` analytic on a full chart target.
>
> **Why route D survives anyway (the key distinction from the σ*-pullback):**
> route D's Liouville step needs `s` **entire** = `AnalyticAt` at *each* point —
> only **local/pointwise** analyticity. It NEVER needs a coefficient analytic on
> a full fixed-chart target (that was submodule condition (1), the thing that
> sank σ*). So work **locally**: at each `x`, the two preimages each sit in
> *some* affine projX chart whose overlap with the relevant preferred chart is a
> neighborhood of that preimage — local analyticity holds there; assemble via the
> locality of `AnalyticOn`.

**The right object:** the coordinate-free **`dx`-coefficient** at a smooth-Y
point `p` — ω paired with `∂/∂x` (the coordinate vector of the affine x-chart).
Concretely, for `p = ⟦inl a⟧`, `a ∈ smoothLocusY`,
```
ωdx ω a (x) := ω.coeff ⟦inl a⟧ ( E_out (lc.symm x) ) · fderiv ℂ ( E_out ∘ lc.symm ) x 1
              ,  lc := affineChartProjX a  (lifted),  E_out := extChartAt ⟦inl a⟧
```
but the deliverable is only its **local** analyticity:
- **`ωdx_analyticAt`**: `AnalyticAt ℂ (ωdx ω a) (x a)` (and on a nbhd of `x a`),
  from: `ω.coeff ⟦inl a⟧` analytic (ω's condition (1) at `⟦inl a⟧`) ∘ the *local*
  transition `E_out ∘ lc.symm` (analytic on the **overlap** nbhd of `a`, via
  `affineLiftChart_mem_maximalAtlas` + `StructureGroupoid.compatible_of_mem_maximalAtlas`),
  × `fderiv` of that transition. **All on a neighborhood of `a` — never the full
  target.**
- **`ωdx_chart_indep`**: `ωdx` is independent of which projX chart represents the
  sheet (same-sheet projX transition derivative `= 1`, so the value agrees) — this
  is what makes `s` well-defined and single-valued.
- **`ωdx_eq`** (optional): relates `ωdx` to `ω.coeff` for downstream use.

**Deliverable of P0:** `def ωdx` + `ωdx_analyticAt` (local) + `ωdx_chart_indep`.
The global `s : ℂ → ℂ` and its entire-ness are assembled in P3 from these local
pieces. (Option 0b — `Quotient.out` hypothesis restriction — remains a fallback
if even the local transition fights `Quotient.out`, but local analyticity should
dodge it.)

## P1 — branch-point removability (Codex, after P0)

**Reading list:** `OddPartDslope.lean` (whole), `AffineForm.lean:460–600` (the
transition `hasDerivAt` lemmas), the P0 output (`cX`, `cX_eq`), `OneForm.lean:60–95`.
**Deliverable:** near a branch point `x₀` (`f(x₀)=0`), with `h := ` the projY
coeff at the branch point, prove `s := cX ω a + cX ω a.invol` extends analytically
across `x₀`. Use: cocycle gives `cX ω a (x) = h(√f)·f'/(2√f)` (and the `a.invol`
version with `−√f`); factor the sum as `(f'/2)·dslope(oddPart h)(√f)` via the
landed helper; `dslope(oddPart h)` analytic + bounded ⇒ `s` bounded near `x₀` ⇒
removable (`analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`).
**This is the math crux; keep it one lemma.**

## P2 — ∞ growth (Codex, after P0)

**Reading list:** `AffineInfinityForm.lean` (the ∞ chart coeff), the ∞-point
structure in `Even.lean`, P0 output. **Deliverable:** `s = O(1/x²)` as `x → ∞`,
from the infinity-chart coordinate `u = 1/x`, `dx = −du/u²`. σ swaps the two ∞
points — handle both.

## P3 — global s, Liouville ⇒ (AI) (Codex, after P1+P2)

**Reading list:** P1, P2 outputs; `EntireGrowth.lean`; `Line/OneForm.lean`
(ℙ¹ Liouville pattern). **Deliverable:** assemble `s` into an entire function on
`ℂ` (same-sheet projX overlaps have transition derivative `1`, so coefficients
*agree* on overlaps — trivial `AnalyticOn` glue), `→0` at ∞ ⇒ `s ≡ 0` by
`differentiable_eq_polynomial_of_growth` (n=0) ⇒ `cX ω a.invol = −cX ω a`, i.e.
(AI). Decide Q4 here: bare Liouville (recommended) vs `genus ℙ¹=0`.

## P4 — L2 from (AI) (Codex, after P3)

**Reading list:** `Form.lean:289–310` (the L2⇒L3 bridge), `AffineForm.lean`
(`squareLocalHomeomorph_symm_eval_analyticOn`), `EntireGrowth.lean`,
`Axioms/HyperellipticLiouville.lean:200–230` (the L2 target statement). **Deliverable:**
`g(x) := cX ω a (x)·√f(x)` is single-valued (AI cancels the √f sign flip), entire,
polynomial-growth ⇒ a polynomial `deg < N/2−1`; discharge
`AX_HyperellipticForm_polynomial_decomposition`.

## Sequencing

P0 (now) → P1 ∥ P2 (parallel Codex) → P3 → P4. Each Codex task: tight reading
list, one lemma, verify with `lake env lean <file>` then `#print axioms`, leave
uncommitted for review (per the Mσ.2 review flow that worked).
