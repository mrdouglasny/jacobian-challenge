# P10 — hyperelliptic boundary-word witness: route note

Lane: P10 (issue #172, G-D half), branch `feat/bw-hyperelliptic`.
Extends the merged g = 1 pattern (#220/#225,
`Jacobians/RiemannSurface/BoundaryWordElliptic.lean`) to the
hyperelliptic family at every genus. Companion gap ledger:
`docs/planning/HYP_CB_BLOCKER.md` (this lane attacks **G-D** — the
`hR1`/`hR2` slots of `nonempty_periodCycleBasis_of_branchCutSystem` —
via `ArcBoundaryWordDataInterior`; **G-C** (H₁) stays a named
hypothesis exactly as in #225's `ellipticPeriodCycleBasisOfH1`).

## Decision 1 — what `h`/`F` are at general genus

Two candidate routes; we implement the **polynomial route** as the
session engine and record the geometric route as the discharge path.

**Route P (polynomial cut pullbacks — implemented).** Take the
primitives `F i := eval (P i)` for a curve-tuned polynomial family
`P : Fin g → ℂ[X]` and `h i := eval (derivative (P i))`. This is the
*literal generalization of g = 1*: there `h = c`, `F = c·z` is the case
`P i = C c * X` with the orientation constant
`c = √|Im (ω₂·conj ω₁)|`. At general g the tuning constant becomes a
**Cholesky factor**: `hgram` (below) is satisfiable iff
`(i)·(AᵀB̄ − BᵀĀ)` is positive-definite Hermitian — i.e. iff R2 is
*true* — and the g = 1 constant `c` is exactly the 1×1 Cholesky factor
of `2·|Im (ω₂·conj ω₁)|`. Consequences, stated honestly:

* every **regularity** field of `ArcBoundaryWordDataInterior` is free
  and *per-genus-uniform* (polynomials are entire);
* the `word_R1` **contour integral side is closed by Cauchy at every
  genus** (`rectBoundaryIntegral_poly_mul`), so the R1 word reduces to
  the bare matrix identity `AᵀB = BᵀA`;
* `nondeg` is **proven** from linear independence of the
  `derivative (P i)` (a nonzero polynomial has finitely many roots;
  the open box image is infinite);
* the two genuinely analytic walls are isolated as the two named
  matrix-level Props (`R1` symmetry + the `R2` Gram word) — these are
  the classical branch-cut period relations, now with **zero manifold
  and zero contour-integral content** (pure identities between
  x-plane interval integrals, see Decision 2).

**Route K (geometric cut chart — the eventual wall discharge).**
`h i := κ*(ω i)` for a slit-plane cut chart `κ : box → HyperellipticOdd`
built from the x-plane slit between branch pairs; the two-sheet
structure makes `∂box ↦` the a/b-cycle crossing word, and `word_R1`/
`word_R2` become the cut-surface boundary-word theorem
(`CUTSURFACE_GAP_ANALYSIS.md` C2 — the interior interface was built so
the polygon-vertex regularity is sufficient). Route K discharges the
same two walls Route P names; the engine landed here consumes either.

## Decision 2 — the g×g block structure of `word_R1`/`word_R2`

Over a `BranchCutSystem S`, every period-matrix entry collapses by
`loop_period_eq` (M3, already proven) to an explicit x-plane interval
integral: connectors cancel, the sqrt lift never appears except through
the form coefficient. We land the **block bookkeeping lemmas**

* `arcAPeriodMatrix_branchCut` / `arcBPeriodMatrix_branchCut` —
  the (i,j) entries of the A/B blocks over `S.loop` as
  `∫₀¹ coeff·x′` integrals (g×g generalization of
  `arcAPeriodMatrix_elliptic`, which was 1×1);
* the wall Props in entrywise form: `word_R1`'s left side at (i,j) is
  `∑ₖ Aₖᵢ·Bₖⱼ − Bₖᵢ·Aₖⱼ` with the explicit integral entries — the
  classical statement "branch-cut a/b-periods of `x^s dx/y` and
  `x^t dx/y` satisfy Riemann I/II", indexable per pair (i,j) with no
  quantifier over abstract forms (the basis expansion to all forms is
  done once, downstream, by `arc_R1_of_periodMatrix_symm` /
  `arc_R2_of_periodGram_posDef` — the #203 quad-sum engine's job).

## Decision 3 — per-genus-uniform vs induction on branch pairs

**Uniform (proven this session, no induction):** `h`, `F`, `hhc`,
`hFc`, `hh`, `hF`, `word_R1`'s Cauchy side, `nondeg`. None of these see
the branch points at all.

**Branch-pair-structured (the walls):** the two matrix identities.
Their eventual discharge (either route) is where the G-B layout enters
— which cuts a given cycle crosses — and proceeds by induction /
case analysis on the branch-pair combinatorics. They are carried as
named hypotheses (`R1Word`, `R2GramWord` Props), never sorries.

## Deliverables of this lane

1. `Jacobians/RiemannSurface/BoundaryWordPolynomial.lean` — the
   general-genus polynomial engine `polyArcBoundaryWordData`
   (any `X`, any loop family): 7 of 9 fields proven from the 3 named
   inputs (`hind`, `hsymm`, `hgram`); `word_R2 := hgram` is the 8th by
   restatement; downstream `periodGram_posDef` is *derived*, not
   assumed.
2. `Jacobians/ProjectiveCurve/Hyperelliptic/BoundaryWord.lean` —
   the family witness `hyperellipticArcBoundaryWordData :
   ArcBoundaryWordDataInterior S.loop cω`, the explicit-integral entry
   lemmas, the named wall Props, and the upgraded conditional
   `nonempty_periodCycleBasis_of_branchCutSystem_boundaryWord`
   (replaces the ∀-forms `hR1`/`hR2` slots of the existing conditional
   witness by the finitary matrix walls + a basis).

## Follow-ups (not this session)

* **Cholesky reduction**: a lemma `PosDef G → ∃ P, hind ∧ hgram`
  converting the R2 wall to bare positive-definiteness of the period
  Gram (needs box-L² polynomial Gram surjectivity onto PD matrices).
* **Route K cut chart** for the geometric discharge of both walls.
* `FiniteDimensional ℂ (HolomorphicOneForm (HyperellipticOdd H h))` +
  `AX_Hyperelliptic_genus` to produce the basis `cω` concretely from
  the #167 `OddForm` layer (`x^k dx/y`).
