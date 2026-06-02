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

## P0 — the transported projX coefficient (DESIGN — do first, Claude/MRD)

`ω.coeff q` is only constrained on the *preferred* chart `extChartAt q`
(`Quotient.out`, arbitrary). The clean object for route D is ω's coefficient in
the **affine projX chart** `affineLiftChart H h a` (deterministic in `a`):

```
cX ω a (z) := ω.coeff ⟦inl a⟧ ( E_out ((affineLiftChart H h a).symm z) )
              · fderiv ℂ ( E_out ∘ (affineLiftChart H h a).symm ) z 1
```
where `E_out := extChartAt ⟦inl a⟧`. **Two design options — pick in P0:**

- **(0a) Transport via the maximal-atlas cocycle.** `affineLiftChart H h a` ∈
  maximal atlas (proven), so ω's cocycle extends to relate `E_out` and
  `affineLiftChart a`; `cX ω a` is then analytic on `(affineChartProjX a).target`
  and equals `ω.coeff ⟦inl a⟧` transported. **Cleanest if** a "coeff satisfies the
  cocycle against any maximal-atlas chart" lemma is cheap to state/prove from
  `SatisfiesCotangentCocycle` + `affineLiftChart_mem_maximalAtlas`. *Likely the
  right call.*
- **(0b) Out-hypothesis restriction.** Mirror `hyperellipticForm_coeff_projX`:
  carry `hQ : Quotient.out q = Sum.inl a` and only define `cX` there; supply
  good witnesses downstream (cf. `quotient_out_of_zero_x`). Lighter to start, but
  pushes the `Quotient.out` pain to P3/P4 (need *all* smooth-Y `a`, not just
  isolated witnesses). *Avoid unless 0a balloons.*

**Deliverable of P0:** a `def cX` + `cX_analyticOn` (analytic on the affine projX
target) + `cX_eq` (relates `cX ω a` to `ω.coeff` so downstream can use it). Once
P0 exists, P1–P4 are Codex-sized.

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
