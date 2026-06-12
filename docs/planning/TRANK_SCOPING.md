# T-RANK scoping — minimal lemma chain

Date: 2026-06-11. Branch `feat/s2-topology` (S2 lane,
`HANDOVER_PARALLEL_ACCOUNT.md` Package 1 stretch goal). Companion to
`GOODCOVER_BLOCKER.md` (answers its GC-2 question) and
`S2_LANE_PROGRESS.log`. **Scoping doc, not a proof** — per the handover,
the deliverable is the minimal lemma chain with difficulty classes.

## 0. Statement and consumer

**T-RANK** (named in `Jacobians/RiemannSurface/HomologyGeneration.lean`):

```
Module.Free ℤ (H1 X x₀)  ∧  Module.finrank ℤ (H1 X x₀) ≤ 2 * genus X
```

where `H1 X x₀ = Additive (Abelianization (FundamentalGroup X x₀))`
(`Homology.lean:41`) and `genus X = Module.finrank ℂ (HolomorphicOneForm X)`
(`Genus.lean:39`) — the *analytic* genus, so T-RANK is a genuine
Betti-vs-analytic comparison, not a definition-chase.

Consumer: `exists_periodGeneratingLoops`
(`PeriodDiscreteness.lean:352`) takes exactly
`[Module.Finite ℤ (H1 X x₀)]` (= T-FG) `+ [Module.Free ℤ (H1 X x₀)]
+ (hrank : finrank ℤ (H1 X x₀) ≤ 2 * genus X)` and yields
`PeriodGeneratingLoops`, whence `discreteTopology` / `exists_basis` /
`finrank_eq` for the period lattice — the B-4 residual of
`AX_PeriodCycleBasis`.

## 1. Decomposition

| Rung | Statement | Class |
|------|-----------|-------|
| TR-0 | `P_b : H1 X x₀ →ₗ[ℤ] (Fin (genus X) → ℂ)`, `h ↦ fun i => loopDevValH1Hom x₀ (b i) h` for a basis `b` of `HolomorphicOneForm X` | **DONE/glue** — `loopDevValH1Hom` exists (`LoopIntegralHom.lean:79`), axiom-free; assembling the vector map is a session |
| TR-DISC | the image `P_b '' H1` is **discrete** in `ℂ^g` (equivalently: `P_b ⊗ ℝ : H1 ⊗ ℝ → ℂ^g` injective; equivalently: a class with all holomorphic periods zero is torsion) | **HARD — the irreducible analytic core**; see §2 |
| TR-CNT | a discrete subgroup of `ℂ^g` is free of rank `≤ 2g` | **EASY** — Mathlib `ZLattice` machinery (`module_free` / rank bounds); restrict to its ℝ-span if not spanning; check exact API at pin |
| TR-TORS | `H1 X x₀` itself is torsion-free | **HARD topologically, but avoidable** — see §3 |

Note the order of quantifiers in TR-CNT: a merely *injective* ℤ-linear map
into `ℂ^g` bounds nothing (`ℤ + ℤ√2` is dense in `ℝ`: rank 2 injects into
real dimension 1). Discreteness is what converts "injects" into "rank ≤
real dimension". This is the same observation as H-lane's "n > 2g
generators do NOT give discreteness" — TR-DISC is exactly where the 2g
count enters, from the other side.

## 2. Routes to TR-DISC (all known proofs)

**(a) de Rham + Hodge** (the classical source). `H1(X,ℝ) → H¹_dR(X)^*` is
injective (de Rham theorem) and `H¹_dR ≅ H^{1,0} ⊕ H^{0,1}` (Hodge /
Dolbeault), both summands of dimension `g` — the keystone just made the
`H^{0,1}` side a theorem (`h1coh_zero_finrank`, `Layer3/Cohomology.lean:60`).
What's missing is the **de Rham comparison layer**: closed/exact smooth
1-forms, integration pairing, and the Dolbeault decomposition of
`H¹(X,ℂ)`. None of this exists in the repo, and Mathlib at our pin has no
de Rham cohomology. Estimate: a multi-week sub-campaign, comparable to a
keystone lane. The honest minimal kernel, if one wants the smallest named
gap rather than the full layer:

> **(TR-DISC-kernel)** a loop class `h : H1 X x₀` with
> `loopDevValH1Hom x₀ ω h = 0` for **all** `ω : HolomorphicOneForm X`,
> AND `(loopDevValH1Hom x₀ ω h).conj`-side vanishing (automatic:
> antiholomorphic periods are conjugates of holomorphic ones on real
> classes) is torsion.

**(b) Riemann bilinear relations over a symplectic cycle basis.**
**Circular here** — the cycle basis is what `AX_PeriodCycleBasis`
provides; we are scoping its discharge.

**(c) Classification of compact surfaces.** Gives `H1 ≅ ℤ^{2g_top}`
directly (plus TR-TORS for free), then `g_top = g` via Riemann–Roch.
Not in Mathlib, classification-grade formalization effort. Out of reach.

**(d) Exponential sheaf sequence.** `0 → ℤ → 𝒪 → 𝒪* → 0` gives
`H¹(X,ℤ) ↪ H¹(X,𝒪)` cheaply from the LES (the connecting
`H⁰(𝒪*) ← H⁰(𝒪)` is surjective). Tempting because the keystone Čech
machinery is live — but **injectivity alone does not bound rank** (the
`ℤ + ℤ√2` problem again), and "the image is a lattice" is Hodge once
more. Also requires Čech theory for the constant sheaf `ℤ`, which the
port doesn't have. Verdict: dead end for the bound; useful context only.

## 3. GC-2 answered, and a re-plumbing dividend

**GC-2 (from `GOODCOVER_BLOCKER.md`) is answered: NO shortcut.** The
keystone machinery (finite-dimensional `H^{0,1}` + period pairing) cannot
bound `rank H1` by itself: any ℂ-valued pairing is blind to torsion
(torsion maps to `0` in `ℂ^g`) and blind to ℤ-rank beyond ℝ-independence
(dense f.g. subgroups exist in any positive dimension). The missing
ingredient is exactly TR-DISC, whose only non-circular source at our pin
is route (a). Consequence for Goal B: T-FG still needs GC-1 (good-cover
existence); there is no Hodge-side bypass.

**Re-plumbing dividend (recommendation).** The consumer chain only ever
uses the **image lattice** `span ℤ (range (loopPeriodVec x₀ b))` in
`ℂ^g`, never `H1` itself as a module. If B-4's residual is restated over

- (T-SPAN′) the developing-value periods ℝ-span `ℂ^g`, and
- (TR-DISC) the image is discrete,

then Mathlib's ZLattice theory gives a rank-2g ℤ-basis of the image
directly — `Module.Free ℤ (H1 ...)` is never needed and **TR-TORS drops
out entirely**. T-RANK as consumed reduces to TR-DISC + T-SPAN′.

**Circularity warning for T-SPAN′.** The existing spanning theorem
`span_range_loopIntegralToH1_eq_top` (`Layer3/PeriodSpan.lean:48`) is NOT
usable for this: `loopIntegralToH1` is *defined* through
`Classical.choice (AX_PeriodCycleBasis x₀)` (`LoopIntegral.lean:70`), so
that statement lives downstream of the axiom being discharged. A
discharge-grade T-SPAN′ must be restated for the axiom-free
`loopDevValH1Hom`. The spanning content ("no nonzero holomorphic form
has all periods zero" + dimension count) is B-3 territory — per
`H_LANE_PROGRESS.log`, B-3 covers the `rank ≥` side; check
`B3_NONDEG_ROUTE.md` for what is proven against `loopDevValH1Hom` vs
against the axiom-routed functional before assuming this rung is free.

## 4. Bottom line

```
T-RANK  ⟸  TR-0 (glue, ~1 session)
          + TR-DISC (named gap, analytic core — route (a), multi-week
            de Rham comparison layer; no shortcut from keystone)
          + TR-CNT (Mathlib ZLattice, ~1 session)
          [+ TR-TORS — avoided by re-plumbing B-4 over the image lattice]
```

Recommended next actions, in order:

1. Re-plumb the B-4 residual over the image lattice (kills TR-TORS,
   shrinks the gap to TR-DISC + T-SPAN′) — pure restatement, 1–2
   sessions, no new mathematics.
2. Prove TR-0 + TR-CNT over named hypotheses `(TR-DISC)` `(T-SPAN′)` —
   everything-over-the-gap, same shape as Goal B's
   `fundamentalGroup_fg_of_goodCover`.
3. TR-DISC itself: open a dedicated route doc for the de Rham comparison
   layer only if/when a lane is willing to fund route (a); pair it with
   the Mathlib Riemannian-geometry watch already noted in
   `GOODCOVER_BLOCKER.md` (GC-1 route 3), since both gaps wait on
   upstream geometry/analysis infrastructure.


## §4 status stamp (2026-06-11, RP-lane)

The issue-#206 re-plumb LANDED (branch feat/b4-image-replumb): the image route
needs NEITHER `Module.Free ℤ (H1)` nor `Module.Finite ℤ (H1)` — discreteness
alone gives freeness/finiteness/rank via Mathlib ZLattice. Residual stack:
T-SPAN′ (PROVEN, B-3) + **TR-DISC** (`DiscreteTopology (loopPeriodLattice x₀ b)`,
the single open input; alternative feeds: the #198 H1 route, or route (a) §2).
