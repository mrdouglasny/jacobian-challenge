# Discharging Liouville L2 / L3 — the last gap in axiom-clean even-genus

*Authored 2026-06-01. Companion to [`AXIOM_AUDIT.md`](../AXIOM_AUDIT.md) Class 2d
and [`genus-theorem-discharge-plan.md`](genus-theorem-discharge-plan.md).*

After task #21, `genus_HyperellipticEven_eq` is **sound** and depends on only
two non-trivial axioms — the Liouville hierarchy L2 and L3
(`Axioms/HyperellipticLiouville.lean`). Retiring both makes the even-genus
theorem fully axiom-clean. This is the classical theorem *"the holomorphic
differentials on `y² = f(x)` are exactly `{x^k dx/y : 0 ≤ k < g}`"* — the
hardest single result left in the repo, and absent from Mathlib.

## The key structural fact (makes L3 ⟸ L2)

L2 (`AX_HyperellipticForm_polynomial_decomposition`) says: every form has
`form.coeff q z = g(z) / √(f(z))` on projX charts at smooth-Y points, for
some polynomial `g`, `deg g < N/2−1`.

`affineProjXCoeff g a hpY z = g.eval z / (squareLocalHomeomorph a hpY).symm (f.eval z)`
(`AffineForm.lean:38`) is **exactly** `(hyperellipticForm g).coeff q z` on
those charts. So **L2's conclusion is `form.coeff = (hyperellipticForm g).coeff`
on smooth-Y projX charts.** Hence:

> **L3 ⟸ L2 + propagation.** Given L2's `g` (low-degree), `form` and
> `hyperellipticForm g` agree on smooth-Y projX charts. If chart-agreement
> there propagates to all charts (branch points + infinity) via the
> now-real cocycle, then `form.coeff = (hyperellipticForm g).coeff` as
> functions, so `form = hyperellipticForm g` (`ext_of_coeff`) — which is L3.

So the work splits into **L2** (the analytic core) and the **propagation**
(L3 from L2). The cocycle they need is now a real theorem
(`hyperellipticEvenCoeff_cocycle_{inl_inr,inr_inl}`, task #21).

## L2 — the analytic core

Define the candidate `G(z) := form.coeff q z · (squareLocalHomeomorph a hpY).symm (f.eval z)`
(`= coeff · √f = coeff · y`) on a projX chart. The classical fact is `G = g(x)`,
a polynomial. Sub-steps:

| Step | Statement | Difficulty | Tool |
|------|-----------|-----------|------|
| **L2-a** | `G` is analytic on each projX chart target | easy | `IsHolomorphicOneFormCoeff` × analyticity of the IFT branch (`squareLocalHomeomorph.symm`) |
| **L2-b** | `G` is single-valued in `x` (independent of sheet / which smooth-Y `q`) | medium | the hyperelliptic involution `σ(x,y)=(x,-y)` acts as `−1` on forms; `dx/y` is σ-anti-invariant. Glue the two sheets' `G` |
| **L2-c** | `G` extends analytically across branch points (`y = 0`, `f = 0`) | **hard** | the projY chart + the cocycle: holomorphicity in the `(x,y)↦y` chart bounds `G` near `y=0` |
| **L2-d** | `G` has polynomial growth `deg < N/2−1` at infinity | **hard** | the affine-infinity chart + cross-summand cocycle: the form's coeff in the `u=1/x` chart bounds `G`'s growth |
| **L2-e** | entire + that growth ⇒ `G` is a polynomial, `deg < N/2−1` | **done** | `differentiable_eq_polynomial_of_growth` (`GeneralResults/EntireGrowth.lean`) |

L2-a/L2-b are tractable now. L2-c and L2-d are the genuine project-specific
complex geometry — each needs the chart-transition behaviour at the branch
locus / at infinity, which is where the now-real cocycle does the work but
the bookkeeping is substantial.

## Propagation — L3 from L2

Two HolomorphicOneForms with the same cocycle that agree on smooth-Y projX
charts agree everywhere:

1. **Affine smooth-Y `q`**: the EvenProj chart at `q` is the projX chart;
   `coeff` is supported on its target (`IsZeroOffChartTarget`) and L2 gives
   the values. Direct.
2. **Branch points (`inl a`, `a ∈ smoothLocusX \ smoothLocusY`)**: the chart
   is projY; relate `coeff` to a neighbouring smooth-Y projX chart via the
   same-summand cocycle (already real in `EvenForm.lean`).
3. **Infinity (`inr b`)**: the affine-infinity chart; relate via the
   cross-summand cocycle (`…_cocycle_inl_inr`/`_inr_inl`, now real).

Each step: `coeff_form q = coeff_(hyperellipticForm g) q` because both sides
satisfy the same cocycle off the smooth-Y charts where they already agree.
~200–400 LOC; uses only landed infrastructure.

## Realistic estimate

- **Propagation (L3 ⟸ L2):** ~1 focused week. Self-contained, uses the real
  cocycle + existing agreement lemmas. **Recommended first** — it collapses
  two axioms into one (L2) and is the more tractable half.
- **L2-a, L2-b:** a few days. Foundational; the `G` construction + sheet
  gluing.
- **L2-c, L2-d:** the hard part, 2–4 weeks. Branch-point regularity and the
  degree-at-infinity bound — genuinely new infrastructure (no Mathlib
  support for meromorphic functions on these curves).

Total to fully axiom-clean even-genus: **roughly 1–2 months** of focused
work, dominated by L2-c/L2-d. This is the canonical-differentials theorem
for hyperelliptic curves; it is the deepest remaining result in the repo.

## Recommended order

1. **Propagation** (L3 ⟸ L2) — collapses to a single axiom, tractable.
2. **L2-a + L2-b** — build `G` and its sheet-independence.
3. **L2-d** (infinity growth) — feeds L2-e (done).
4. **L2-c** (branch points) — the last and hardest piece.
