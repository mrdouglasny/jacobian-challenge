# Decision: how to prove σ-anti-invariance toward Liouville L2

*Authored 2026-06-02 (Claude). A strategy-fork decision doc, for review by Codex
and by MRD. Supersedes the σ*-pullback plan of [`Msigma3-codex-plan.md`](Msigma3-codex-plan.md)
pending this decision. Context: [`genus-L2-execution-roadmap.md`](genus-L2-execution-roadmap.md),
[`Msigma-codex-handoff.md`](Msigma-codex-handoff.md).*

## 0. The single fact we actually need

L2 (`AX_HyperellipticForm_polynomial_decomposition`) requires: for every
holomorphic 1-form `ω` on the even-degree hyperelliptic curve
`X = HyperellipticEvenProj H`, the projection-to-`x` chart coefficient is
`ω.coeff(q, z) = g(z) / √f(z)` for a single polynomial `g`, `deg g < N/2 − 1`,
**uniformly over all smooth-Y points `q`**. The load-bearing lemma en route is
**σ-anti-invariance**:

> **(AI)** On the smooth-Y (projection-to-`x`) charts, `ω.coeff(σq, z) = −ω.coeff(q, z)`,
> where `σ = hyperellipticEvenInvol H` is the hyperelliptic involution `(x,y)↦(x,−y)`.

`σ` is already built and **proven `ContMDiff`** (`hyperellipticEvenInvol_contMDiff`,
commit `3890d91`). The question is purely: **what is the cleanest path to (AI)?**

## 1. The representation, and the condition that bites

`HolomorphicOneForm X` is the submodule of `coeff : X → ℂ → ℂ` satisfying
(see `Jacobians/RiemannSurface/OneForm.lean`):

1. `IsHolomorphicOneFormCoeff`: `∀ x, AnalyticOn ℂ (coeff x) (extChartAt x).target`
   — analytic on the **full** chart target.
2. `SatisfiesCotangentCocycle`: the chart-overlap transformation law with a
   `fderiv` factor.
3. `IsZeroOffChartTarget`.

The preferred chart `extChartAt x` is fixed by the `ChartedSpace` instance and
**chosen via `Quotient.out`** — arbitrary among compatible charts. Chart
sources/targets are **local**: `affineChartProjX` is built from
`squareLocalHomeomorph`, a local √f branch via the inverse-function theorem
(`ContDiffAt.toOpenPartialHomeomorph`). So a projX chart covers a *disk-like*
region of the `x`-line, **not** a whole sheet.

## 2. The obstruction that killed the σ*-pullback plan (Mσ.3)

The roadmap's plan was to build `σ* : Ω¹(X) → Ω¹(X)` as a submodule element with
`(σ*ω).coeff q z = ω.coeff(σq)(e_{σq}(σ(e_q.symm z))) · fderiv(e_{σq}∘σ∘e_q.symm) z 1`,
then run "`ω + σ*ω` is σ-invariant ⇒ 0". **This fails condition (1):** the term
`e_{σq}∘σ∘e_q.symm` is only meaningful where `σ(e_q.symm z) ∈ (e_{σq}).source`,
and `σ(source e_q) ≠ source e_{σq}` in general — the projX chart source is one
local sheet, σ swaps sheets, and `Quotient.out` may pick an unrelated preferred
chart at σq. So the fixed-target-chart formula is **not even correct**, let alone
analytic, on the full `(e_q).target`. The value is well-defined and *locally*
analytic, but no single fixed-chart closed form is analytic on the whole target.
(Discovered while implementing; it is also what made Codex thrash for hours.)

This is the same flavor as the still-axiomatized cross-summand compat axioms
`affineLiftChart_compat_infinityLiftChart` — cross-chart gluing is the hard part.

## 3. The candidate routes

### A — "rotated chart" `c_q := chartAt q ∘ σ`
σ becomes the identity in `c_q`, so `σ*coeff(q)(z)` = "ω's coefficient in the
maximal-atlas chart `c_q`". **Not self-contained:** expressing ω's coefficient in
a *non-preferred* chart from the preferred-chart data is exactly the cocycle, and
its full-target analyticity collapses back into B or C. Rejected.

### B — σ*-pullback by open-cover + glue (continue Mσ.3)
Define `σ*coeff(q)` locally (a fixed preferred chart per piece of the target),
glue analyticity via locality of `AnalyticOn`, and separately prove the cocycle.
**Honest, axiom-clean, but the heaviest:** glues a *cocycle family with `fderiv`
factors* AND must re-prove cocycle/functoriality. ~250–400 LOC, brittle. This is
"the gluing nightmare" Gemini ranked worst.

### C — abstract cotangent bundle (Gemini's #1)
Define σ* abstractly as a holomorphic section `q ↦ ω_{σq} ∘ mfderiv σ q` of the
cotangent bundle; derive the coeff formula as a *theorem*; full-target
analyticity is then a free consequence of the global definition + identity
theorem. **Cleanest in the abstract — but a mirage for THIS codebase:** our
`HolomorphicOneForm` *is* the cocycle submodule; there is no cotangent-bundle /
`ContMDiffSection` layer, and C requires first building the **equivalence**
`(cocycle submodule) ≃ (holomorphic cotangent sections)` — a large independent
project, on top of Mathlib's still-thin complex cotangent bundle. Trades our
concrete crux for a much bigger infrastructure bill.

### D — avoid σ* entirely; prove (AI) directly via a symmetric scalar  ★ recommended
**Never construct σ* as a submodule pullback.** Use σ only as the (already
proven) smooth **point map**. Define the *scalar*

> `s := ω.coeff(q, ·) + ω.coeff(σq, ·)`  on the common projX `x`-target of the
> two sheets `q` and `σq = σ·q` over the same `x`-values.

`s` is **symmetric under the sheet swap `q ↔ σq`**, hence single-valued in `x`
(no √f monodromy). Then show `s ≡ 0`:

- **analytic** on its `x`-domain (sum of two `AnalyticOn` coefficients);
- **branch points** `x₀` (`f(x₀)=0`): `s` extends analytically — boundedness from
  ω being holomorphic in the projY chart there ⇒ removable singularity
  (`Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`);
- **`x → ∞`** (the two ∞ points, swapped by σ): `s = O(1/x²)` from the ∞ chart;
- **entire + `→0` ⇒ `s ≡ 0`** by the Liouville/growth machinery **already in the
  repo** (`differentiable_eq_polynomial_of_growth`, `Line/OneForm.lean`).

`s ≡ 0` is exactly (AI). Then L2 follows as planned: `g(x) := ω.coeff(q,x)·√f(x)`
is now single-valued (anti-invariance makes the √f sign-flip cancel the coeff
sign-flip), entire, polynomial-growth ⇒ a polynomial of degree `< N/2−1`.

**Why D is the right call here.** It (i) deletes the σ*-submodule object and its
full-target-analyticity crux entirely; (ii) uses σ only as a point map (done);
(iii) reuses the *exact* removable-singularity + Liouville machinery L2 needs
anyway — so it adds almost no infrastructure beyond unavoidable L2 work; (iv)
needs no quotient manifold and no cotangent bundle. Gemini ranked D second only
because it assumed the heavy *trace-to-ℙ¹-via-quotient-manifold* variant; the
symmetric-scalar variant here is strictly lighter.

## 4. Honest accounting of D's residual cost

D is **not** gluing-free — projX charts are local (§1), so `s` lives per
chart-pair on a local `x`-disk while the Liouville step needs `s` as one entire
function on `ℂ` (≅ `ℙ¹∖∞`). But the gluing is **nearly trivial**, for a reason
that does not hold for B: the **same-sheet projX↔projX transition is the identity
`x ↦ x` (derivative exactly `1`)** — `e_q.symm x = (x, √f x)`, `e_{q'}` of that is
`x` again. So by ω's cocycle the coefficients *literally agree* on overlaps,
`coeff(q,·) = coeff(q',·)` where both are defined, and the local pieces of `s`
assemble by a bare `AnalyticOn`-on-a-union argument — **no `fderiv` factor, no
transition algebra**. This is the structural reason D is cheaper than B (which
glues a cocycle family *with* surviving derivative factors). The assembly is
morally "`s` descends to a holomorphic function on `ℙ¹`, which is `0`".

Where the **real** work concentrates (for the evaluator to pressure-test):

- **Q1 (single-valuedness / monodromy).** `coeff(q,·)` over a full `x`-loop is
  multivalued (√f monodromy swaps the sheets). The claim is that the *symmetric*
  `s = coeff(q,·)+coeff(σq,·)` is invariant under that swap, hence single-valued.
  Confirm this is what lets `s` (unlike either summand) extend to a single global
  function, and that it is clean to state without an explicit monodromy argument
  (e.g. just: on every overlap the two local definitions agree because swapping
  the sheet label permutes the two summands).
- **Q2 (the crux — branch-point boundedness).** Each summand **blows up** like
  `1/√f` at a branch point `x₀` (the projX↔projY transition derivative
  `dy/dx = f'/(2√f) → ∞`). `s` is removable **only because the two `±1/√f`
  singularities cancel** in the symmetric sum. This cancellation — via the projY
  chart relation at the merged branch point (`q, σq → b`, σ fixes `b`) — is the
  genuine technical content of D. Verify it actually cancels (sign/coefficient
  bookkeeping), since the whole route rests on it.
- **Q3 (∞ growth).** `s = O(1/x²)` at the two ∞ points (σ swaps them): confirm
  the ∞-chart computation gives this for the symmetric sum.
- **Q4 (assembly choice).** Liouville directly on `s` (self-contained, re-walks
  branch/∞ bookkeeping) vs. packaging `s dx` as a `HolomorphicOneForm
  ProjectiveLine` and invoking the **proven** `genus ℙ¹ = 0` (reuses a result but
  needs ℙ¹-chart gluing of `s dx`). Which is less Lean work given our assets?

## 5. What we keep / discard

- **Keep** (unchanged, on `main`): `hyperellipticEvenInvol` + `…_contMDiff`
  (`3890d91`) — σ as a smooth point map is used by D.
- **Discard / park**: the `msigma3` branch scaffold (`pullbackInvolutionCoeff`,
  `pullbackInvolution` linear map, `031618f`). Correct as far as it goes but
  unused under D. Keep the branch as a record of the obstruction; do not merge.
- **Supersede**: `Msigma3-codex-plan.md` (route B). Mark it superseded by this doc
  if D is chosen.

## 6. The decision

**Recommendation: Route D** (symmetric-scalar direct anti-invariance), with the
assembly framed as "`s` descends to `ℙ¹`; reuse `genus ℙ¹ = 0` if it shortens the
branch/∞ bookkeeping, else bare Liouville." Rationale: least net infrastructure
for this codebase, no new axioms, reuses L2 machinery, σ stays a point map.

**Asks of the evaluator (Codex):**
(a) find any *mathematical* hole in D — above all **Q2 (the `±1/√f` cancellation
that makes `s` bounded at branch points)** and **Q1 (single-valuedness of the
symmetric `s`)**; if either fails, D collapses.
(b) judge **Q4** — `genus ℙ¹ = 0` descent vs. bare Liouville, whichever is less
Lean work given our assets.
(c) sanity-check that D **truly avoids the §2 full-target-analyticity crux**:
`s`'s analyticity should only ever be needed where both summands are genuinely
defined (their common projX `x`-target), never as a fixed-chart pullback on a
full target.
(d) if D has a fatal flaw, state whether B or C is the lesser evil, and why.
