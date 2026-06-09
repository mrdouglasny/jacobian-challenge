# Discharge plan — the odd-atlas infinity-chart cluster (7 axioms, Class 2c)

*2026-06-09 scoping (stretch deliverable of the autonomous run; tracker #133,
sub-issues #58–#64). The largest remaining 2c cluster.*

## The cluster (`OddAtlas/InfinityChart.lean`)

| Axiom | Content |
|---|---|
| `infinityInverseMap` | the local inverse `t ↦ (x(t),y(t))`, `x ~ 1/t²`, `y ~ 1/t^{2g+1}` on a punctured disk |
| `infinityChart` | `OpenPartialHomeomorph (HyperellipticOdd H h) ℂ`, forward `(x,y) ↦ y/x^{g+1}`, `∞ ↦ 0` |
| `infinityChart_mem_source` | `∞` in the source |
| 4 compat axioms | `infinityChart` vs the lifted affine X/Y charts, both directions |

**History/landmine:** an earlier Phase-3 "discharge" of `infinityInverseMap`
was REVERTED in review — its `def` picked an *arbitrary* polynomial root
(`Classical`-style), not the analytic branch. Whatever we do must construct
the branch *analytically*.

## Why odd ∞ is a branch point (the math)

For odd `deg f = 2g+1`, the smooth completion has ONE point over `x = ∞` and
it is a **ramification point** of the 2:1 cover `x : X → ℙ¹` (vs. the even
case: two unramified points, handled by `reverseData` + the ordinary affine
atlas). Local coordinate at ∞: `t` with `x = 1/t²·u(t)`, `y = t^{-(2g+1)}·v(t)`
— i.e. the chart inverts a map with a **square-root branch**, exactly the
structure of the finite branch points `y² = f(x)` at roots of `f`.

## The route: reuse the PROVEN finite-branch machinery

The finite-branch analytic machinery already exists and is discharged:
`AffineForm.lean`'s `squareLocalHomeomorph` (zero-exclusion + no-critical-
points proven in PR #78) with its API
(`squareLocalHomeomorph_symm_eval_analyticOn`, `_symm_eq_of_mem`,
`_symm_hasDerivAt`, `_symm_ne_zero`). Plan:

1. **Conjugate ∞ to a finite branch point.** Apply the even-atlas
   `reverseData`-style move: substitute `x = 1/u` and clear denominators —
   the curve near `x=∞` becomes `w² = u·r(u)` near `u = 0` with
   `r(0) = lc(f) ≠ 0` (odd degree ⇒ the extra factor `u` survives —
   this IS the ramification). Concretely `w := y/x^{g+1}`, `u := 1/x`
   satisfy `w² = u^{2g+2}·f(1/u) =: F̃(u)` with `F̃(0)=0`, `F̃'(0) ≠ 0`.
2. **Build `infinityInverseMap` honestly**: `t ↦ (x(t), y(t))` where
   `u(t) := (the analytic local inverse of t ↦ t²·c(t)-form)` — i.e. invert
   `t = w`-coordinate via `squareLocalHomeomorph`-style composition: since
   `w² = F̃(u)` with simple zero at 0, `u = G(w²)`-NO: `u` is an analytic
   function of `w` directly: `w² = F̃(u)`, `F̃` invertible at 0 (simple zero)
   ⇒ `u = F̃⁻¹(w²)` with `F̃⁻¹` the IFT inverse (the polynomial local inverse
   from `polynomialLocalHomeomorph`, also proven in #78). **No square root
   needed in this direction** — that's the key simplification: the chart
   coordinate IS `w = t`, and `u = F̃⁻¹(t²)` is manifestly analytic; then
   `x = 1/u`, `y = w/u^{g+1}` on the punctured disk (`u ≠ 0` for `t ≠ 0`
   small, by `_symm_ne_zero`-style arguments).
3. **`infinityChart`**: forward `(x,y) ↦ y/x^{g+1}` (already the stated
   form), inverse from step 2, glued at `∞ ↦ 0` over the `OnePoint`
   topology (the even atlas's `OnePoint` handling + `HyperellipticOdd`'s
   existing topology are the template).
4. **mem_source + 4 compat axioms**: with both defs real, the compat proofs
   are `ContDiffOn` of explicit compositions — rational maps in `t` and the
   IFT inverse; same texture as the even-atlas compat (#109/#111) and the
   `chart_transition_eq_Y_Y`-style equality lemmas.

## Sequencing & estimate

PR 1: steps 1–2 (`F̃`, its IFT inverse, `infinityInverseMap` as a real def +
its analyticity/puncture lemmas). PR 2: step 3 (the chart + `mem_source`,
−3 axioms). PR 3: the 4 compat axioms (−4). Total ballpark: comparable to
the even-atlas infinity work — **~2–3 sessions**. Risk: the `OnePoint`
gluing details and the `t ↦ t²` vs `w²=F̃(u)` orientation bookkeeping
(the reverted attempt failed exactly on branch selection — step 2's
"invert F̃, never choose a root" design eliminates the choice entirely).

## Acceptance

Each PR: `lake build` green, `#print axioms` of every new def/theorem =
standard-3 (+ the not-yet-discharged remaining odd axioms where they're
consumed), guard reconciled, no `Classical.arbitrary`/root-picking anywhere
in the branch construction.
