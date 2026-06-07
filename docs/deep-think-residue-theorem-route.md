# Deep-think query — cleanest route to the residue theorem on a compact Riemann surface (Lean 4 / Mathlib)

## Role & ask

You are a research collaborator on a Lean 4 + Mathlib formalization of Riemann
surface theory (Kevin Buzzard's "Jacobian Challenge"). We need to decide the
**cheapest correct route** to formalize the **residue theorem on a compact
Riemann surface**:

> For a meromorphic 1-form `ω` on a compact, connected Riemann surface `X`,
> the sum of all its residues is zero:  `∑_{P ∈ X} res_P(ω) = 0`.

This is the crux of the `⊇` direction of Abel's theorem (principal ⇒ kernel of
Abel–Jacobi), the deepest remaining axiom in our project. An earlier internal
plan estimated this at **2000–3500 LOC**, dominated by building **Stokes'
theorem on a 2-manifold with boundary on a charted space from scratch** (Mathlib
has no such thing at our pin). We suspect that estimate is pessimistic given the
infrastructure we already have, and we want your judgment on the route before we
commit weeks of work.

**Deliverable we want from you:** a recommended route with a concrete,
file-by-file Lean decomposition, realistic LOC at our pin, the single
load-bearing lemma that collapses most of the work, and exact Mathlib lemma
names wherever you can give them (flag where you're unsure of the exact API).

## Mathlib pin

Recent Mathlib (late 2025 / early 2026). Please state explicitly where you are
unsure whether a lemma exists at this pin, and give the name you'd search for.

## What we ALREADY have in the project (reuse these — do not re-derive)

### A. Meromorphic function field (real defs, not stubs)
- `MeromorphicFunctionField.Rep X` — a representative of a meromorphic function
  on `X` (a structure wrapping `X → ℂ` with meromorphy data).
- `orderAt p (f : X → ℂ) : ℤ∞` (WithTop ℤ) — order of vanishing/pole at `p`
  (Wallace `VanishingOrder`, chart-local Laurent order).
- `orderSupport_finite (f : Rep X) : {p | orderAt p f ≠ 0}.Finite` — **finite
  support of the order divisor** (uses `X` compact).
- `orderFinsupp (f : Rep X) : X →₀ ℤ` and
  `divisor (f : Rep X) : Divisor X := Finsupp.toFreeAbelianGroup (orderFinsupp f)`.
- `divisor_mul`, `divisor_one`, `orderAt_mul`, `orderAt_inv`, etc. — the divisor
  is a group hom to `Divisor X = FreeAbelianGroup X`.

### B. Wallace-vendored analytic substrate (sorry-free, axiom-free)
- `BranchedCover`, `VanishingOrder` (`orderAt`), `CotangentBundle`,
  `HolomorphicMap`.
- **Conservation of number** — the key one:
  ```
  theorem weightedFiberConservation_of_contMDiff
      [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y]
      [CompactSpace X] [T2Space X] [PreconnectedSpace X] [T2Space Y]
      {f : X → Y} (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ⊤ f)
      (hnonconst : ¬ ∃ y₀, ∀ x, f x = y₀)
      (finite_fiber : ∀ y, (f ⁻¹' {y}).Finite) (y₀ : Y) :
      -- the weighted fiber sum ∑_{p ∈ f⁻¹(y)} (localOrder f p y) is locally
      -- constant in y, hence constant = deg f  (a LocallyConstant invariant)
  ```
  This already gives us "∑ over a fiber of a local multiplicity is a
  locally-constant (hence global) invariant" — the engine behind
  `AX_BranchLocus` (now a **theorem**) and `degree`.

### C. Arc / contour integration on X (from our homotopy-invariance workstream)
- `canonicalArcIntegral (γ : AnalyticArc X) (form : HolomorphicOneForm X) : ℂ`
  `:= ∫ r in (0:ℝ)..1, canonicalIntegrand γ form r` — integral of a HOLOMORPHIC
  1-form along a piecewise-analytic arc, via a moving-chart integrand.
- `canonicalArcIntegral_homotopy_invariant` — **homotopy invariance** of that
  integral (rel endpoints), proven from scratch.
- `canonicalArcIntegral_add`, `_smul`, `_reverse`, `_trans`.
- `developingValue` + `developingValue_basepoint_indep` — the multivalued
  primitive `∫_{x₀}^{x} form` realized as a developing map.
- `loopIntegralToH1` — loop integrals factor through `H₁(X)`; period lattice
  infrastructure (`periodLatticeInBasis`, `AX_AnalyticCycleBasis` gives a
  symplectic basis).
  **IMPORTANT CAVEAT:** all of `canonicalArcIntegral` etc. are currently typed
  for **holomorphic** 1-forms (`HolomorphicOneForm X`), NOT meromorphic ones. A
  meromorphic ω is holomorphic on `X ∖ poles`. Reusing this machinery for the
  residue theorem requires integrating ω over arcs/loops that avoid the poles.

### D. Holomorphic 1-form API
- `structure HolomorphicOneForm X` with `coeff : X → ℂ → ℂ` (chart-local
  coefficient: `form.coeff x z` is the coefficient in the chart at `x`).
- `IsHolomorphicOneFormCoeff X coeff := ∀ x, AnalyticOn ℂ (coeff x) (extChartAt 𝓘(ℂ) x).target`.
- `SatisfiesCotangentCocycle` — the `coeff` family transforms as a cotangent
  vector across chart overlaps (`fderiv` chain rule).

### E. Discharged / available
- `AX_BranchLocus` is now a **theorem** — finite fibers + fiber-degree are
  theorem-backed.
- `AX_ofCurve_inj` (Abel injectivity, positive genus) is a **theorem**, proved
  via the `developingValue` / homotopy-invariance route (NOT via residues).

## The core questions

**Q1 — Can we AVOID building full manifold Stokes-with-boundary?**
Rank these candidate routes by total new-infrastructure cost at our pin, and
recommend one:

- **(a) Fundamental-polygon edge-cancellation.** Realize `∑res = (1/2πi)
  ∮_{∂Π} ω` where `Π` is a fundamental `4g`-gon, and argue the boundary integral
  is `0` because identified edges are traversed in opposite orientations and ω
  agrees across the gluing (the side-pairing is the deck/identification map).
  **Can this be done using ONLY our homotopy-invariant `canonicalArcIntegral`
  machinery** (edges are arcs; identified edges give `canonicalArcIntegral(e) +
  canonicalArcIntegral(reverse e') = 0` since ω pulls back to itself), plus a
  local "winding ⇒ residue" computation in a chart around each pole? What is the
  hard part — constructing the polygon/triangulation, or the puncture-limit
  `∮_{|z-p|=ε} ω → 2πi·res_p`?

- **(b) Reduce to Mathlib planar theory + partition of unity.** Cover `X` by
  finitely many charts; on each chart image (open ⊆ ℂ) use Mathlib's
  `Complex`/`circleIntegral`/Cauchy theory; glue with a partition of unity so
  the chart-overlap terms cancel. Does Mathlib's planar contour API
  (`Complex.circleIntegral`, `circleIntegral_div_sub_of_...`, the Cauchy
  integral formula, `Complex.residue` if it exists?) suffice, and is the
  partition-of-unity bookkeeping cheaper than (a)?

- **(c) Argument-principle / conservation-of-number first.** Prove the special
  case `ω = df/f` (logarithmic derivative of a meromorphic function `f`) via our
  `weightedFiberConservation` (`∑ ord_P(f) = 0`, i.e. `deg(div f) = 0` =
  #zeros − #poles for a map to ℙ¹). Then bootstrap to general meromorphic ω.
  **Is the bootstrap from `df/f` to general ω actually easy?** (Classically:
  every meromorphic ω = `f · ω₀` for a fixed ω₀ and meromorphic `f`, and
  `res(f ω₀)` relates to... — please verify whether this bootstrap is clean or
  whether it secretly needs the full residue theorem anyway. My worry: the
  argument principle gives `∑ res(df/f) = 0` which is `∑ ord = 0`, a statement
  about INTEGER residues only — it may not reach general complex residues.)

- **(d) Slick route via ℙ¹.** Push ω forward (or pull a function back) to ℙ¹ and
  use that `∑res = 0` is trivial on ℙ¹ by an explicit partial-fractions /
  residue-at-∞ computation. Does the trace/pushforward needed here exist cheaply,
  or does it reintroduce the (hard, still-axiomatic) `pushforwardOneForm` trace?

**Q2 — The puncture-limit lemma.** Whichever route, we likely need
`lim_{ε→0} ∮_{|z-p|=ε} ω = 2πi · res_p(ω)` in a chart. Does Mathlib have this (or
`Complex.residue` + a circle-integral-equals-residue lemma)? Give exact names.
If not, estimate its cost — is THIS the real load-bearing lemma rather than
Stokes?

**Q3 — Is `∑res = 0` even the right FIRST target,** or should we first prove the
**argument principle** (`∑ ord_P(f) = 0` via `weightedFiberConservation`, which
we nearly have) and treat the general residue theorem as a later, separate
build? We care about (i) what unblocks Abel's `⊇` direction with least work, and
(ii) honest sequencing.

**Q4 — Concrete Lean decomposition.** Given your recommended route, give a
file-by-file plan (file name, what it proves, realistic LOC at our pin reusing
A–E above), and name the single lemma that, if it exists in Mathlib or is cheap,
collapses most of the work. Be explicit about which of our existing pieces
(A–E) each step reuses.

## Constraints / preferences
- Strongly prefer reusing the homotopy-invariant arc-integral machinery (C) over
  building fresh manifold-Stokes.
- No new axioms — we want a theorem, sorry-free.
- Honest LOC and honest "Mathlib doesn't have this" flags. If a route looks
  cheap but hides a 1500-LOC dependency, say so.
- If you think the earlier 2000–3500 LOC / full-Stokes estimate is actually
  correct and there is no shortcut, say that too — a clear "no shortcut, here's
  why" is valuable.
