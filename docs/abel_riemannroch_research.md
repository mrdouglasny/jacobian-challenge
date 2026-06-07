# Research — cheapest Lean path to `abelJacobi_twoPoint_ne_zero` (#3, "Abel's theorem")

Read-only research note for `/home/rado/jacobian`. Companion to the period-lattice note
`docs/period_lattice_realbasis_research.md`. Verified against the repo's Mathlib pin
(`8e3c989104da`, Lean `v4.30.0-rc1`) and the Forster/Griffiths–Harris PDFs in the repo root.

Legend: **[VERIFIED]** = confirmed by reading Mathlib source / loogle / leansearch this session;
**[BOOK]** = read off the Forster/Kleinerman PDFs this session; **[BELIEVED]** = standard but not
re-derived here.

---

## 0. Bottom line (recommendation)

**Do NOT try to discharge `abelJacobi_twoPoint_ne_zero` from scratch, and do NOT route it through
Riemann–Roch.** Three findings drive this:

1. **The target is exactly the injectivity of Abel–Jacobi on `Pic⁰`, restricted to two points
   (Forster Thm 21.7 + Abel's Theorem 20.7).** In this repo's encoding it is *literally* the statement
   "`periodVec(smoothPath P Q) ∉ truePeriodLattice X`" for `P ≠ Q`, `genus ≥ 1`. **[BOOK/VERIFIED]**

2. **It is NOT a corollary of #7 (period-lattice full-rank).** Full-rank-ness of `Per` says the
   lattice is discrete and spans `ℝ²ᵍ`; it says *nothing* about whether the specific open-path period
   `∫_Q^P ω⃗` happens to be a lattice point. There is no "meet in the middle" that makes #3 fall out of
   #7 — they are logically independent. (Detail in §6; this was the highest-value question and the
   answer is a clear *no*.) **[VERIFIED by structural analysis]**

3. **The genuinely cheapest *honest* path is to keep #3 as an isolated, precisely-stated classical
   input — Abel's Theorem itself — exactly as the repo already isolates `exists_cutSurface` (#7) and
   `MonodromyLiftFamily`/`PreimageCycle` (#6/#8).** The full from-scratch proof (either direction of
   Abel) needs machinery Mathlib does not have (weak solutions of divisors via the Dolbeault/`∂̄`
   solvability `Forster 19.10/12`, or third-kind differentials + reciprocity), at a cost
   (~3–6k LoC of genuinely new manifold analysis) that dwarfs #7 and has no Mathlib scaffolding.

If a *proof* (not an isolated axiom) is wanted, the cheapest realistic route reuses the repo's
**already-built, axiom-clean Trace machinery** (`traceForm`, `pushforward_pullback`, the
`Discharge/Manifold` Riemann–Hurwitz degree layer). That gives the *necessity* half of Abel cheaply,
but the repo needs the *sufficiency* half (construct `f`), which Trace does **not** provide. See §2
for the exact split and the one viable reformulation that avoids constructing `f`.

**Recommended action:** promote `abelJacobi_twoPoint_ne_zero` to an isolated input named
`exists_meromorphic_of_abelJacobi_zero` (or keep the single `sorry` but re-document it against
**Forster §20.7a + §21.7**, not "§21.5 + Riemann–Hurwitz" which is the wrong/over-strong citation —
see §7). Budget any real discharge attempt at the same scale as #7 (2–4k LoC) **only** if the
`∂̄`-solvability route below is taken; otherwise it is strictly larger.

---

## 1. What `abelJacobi_twoPoint_ne_zero` is asserting

### 1.1 The Lean statement (`Jacobians/Abel.lean:666`)

```lean
theorem abelJacobi_twoPoint_ne_zero (h : 0 < genus X) {P Q : X} (hPQ : P ≠ Q) :
    abelJacobi ⟨twoPointDivisor X P Q, twoPointDivisor_mem_degZero X P Q⟩ ≠ 0
```

Unwinding the definitions:

- `abelJacobi D = ∑_{P ∈ supp D} (D P) • mk(periodVec (smoothPath P₀ P))` in
  `(Fin g → ℂ) ⧸ truePeriodLattice X`, `P₀ = Classical.arbitrary X`.  (`Abel.lean:579`)
- `periodVec γ i = lineIntegral (periodBasisForm X i) γ` = `∫_γ ωᵢ`, the vector of integrals of a
  fixed ℂ-basis `ω₁..ω_g` of `HolomorphicOneForms X` (`SmoothPathCore.lean:101`,
  `genus X := finrank ℂ (HolomorphicOneForms X)`).
- The repo already proves (`abelJacobi_twoPointDivisor`, `Abel.lean:593`, **no sorry**):
  `abelJacobi (P − Q) = mk(periodVec(sp P₀ P)) − mk(periodVec(sp P₀ Q))`.
- `ofCurve P₀ Q = mk(periodVec(sp P₀ Q))` (`Jacobians.lean:164`). So
  `abelJacobi (P − Q) = ofCurve P₀ P − ofCurve P₀ Q`.

Therefore, using `ofCurve_basepoint_change` (proven), the statement is **equivalent** to:

> **`periodVec (smoothPath P Q) ∉ truePeriodLattice X`** for `P ≠ Q`, `genus X ≥ 1`. **[VERIFIED]**

i.e. the Abel–Jacobi integral `(∫_Q^P ω₁, …, ∫_Q^P ω_g)` along the path is **not** equal to any
period of any closed loop. Equivalently `ofCurve P₀` is injective at `{P,Q}` — which is exactly how
the repo consumes it: `ofCurve_inj` (`Jacobians.lean:275`) derives `Function.Injective (ofCurve P)`
from this one leaf.

### 1.2 The classical theorem behind it

This is **the injectivity of the Abel–Jacobi map on degree-0 divisor classes**, which is precisely
the kernel computation in **Forster Theorem 21.7** (p. 171): the map
`Φ : Div⁰(X) → Jac(X)`, `Φ(D) = (∫_c ω₁,…,∫_c ω_g) mod Per`, has `ker Φ = Div_P(X)` (principal
divisors), hence descends to an **injective** `j : Pic⁰(X) ↪ Jac(X)`. **[BOOK, Forster p.171]**
The kernel statement `ker Φ = Div_P(X)` is **Abel's Theorem (Forster 20.7, p.163)**:

> **Abel (Forster 20.7).** A divisor `D` with `deg D = 0` is the divisor of a meromorphic function
> iff there is a 1-chain `c` with `∂c = D` and `∫_c ω = 0` for every `ω ∈ Ω(X)`. **[BOOK]**

For the two-point divisor the cleanest mathematical statement is:

> **Target (cleanest form).** Let `X` be a compact Riemann surface of genus `g ≥ 1` and `P ≠ Q`.
> Then `P − Q` is **not** the divisor of any meromorphic function; equivalently
> `∫_Q^P ω⃗` is not a period, i.e. `ofCurve P₀ P ≠ ofCurve P₀ Q`.

The reason `P − Q` is never principal for `g ≥ 1`: a meromorphic `f` with `(f) = P − Q` has exactly
one simple pole and one simple zero, so `f : X → ℙ¹` has degree 1, hence is a biholomorphism,
forcing `X ≅ ℙ¹` (`g = 0`) — contradiction. **[BOOK, Forster 20.1 + the degree-1 ⟹ iso fact]**
(Forster makes the genus-1 endpoint explicit: **Thm 21.10**, `J : X → Jac(X)` is an isomorphism for
`g = 1`, so already at `g = 1` the map `X → Jac` is injective. p.172.) **[BOOK]**

---

## 2. The cheapest classical proof to formalize (and the sufficiency/necessity trap)

There are exactly two pre-20th-century elementary proofs of Abel's theorem; both are in the repo's
own references. **Neither uses sheaf cohomology**, but each needs a different missing analytic engine.

### 2.1 Route A — Forster §20 (Trace + weak solutions). THE repo-native route.

Forster's proof (read in full this session, pp.159–164) is the one to mirror because **its analytic
engine is the Trace of a holomorphic 1-form under a branched cover — which this repo has already
built and verified axiom-clean** (`traceForm`, `traceForm_comp` #5, `traceExtendsAt_branchPoint` #4,
plus the whole `Discharge/Manifold` degree/Hurwitz layer). The two halves:

- **Necessity (20.7b, p.164): `D principal ⟹ ∫_c ω = 0 ∀ω`.** Proof: `f` meromorphic with `(f)=D`
  is an `n`-sheeted cover `f : X → ℙ¹`; for `ω ∈ Ω(X)` form `Trace(ω)` on `ℙ¹`; since `Ω(ℙ¹)=0`,
  `Trace(ω)=0`; and `∫_c ω = ∫_γ Trace(ω) = 0` where `γ` joins the poles to the zeros of `f`.
  **This is exactly the repo's `traceForm` + `pushforward`/`lineIntegral_pullback` content.** **[BOOK]**

- **Sufficiency (20.7a, p.164): `∫_c ω = 0 ∀ω ⟹ D principal`.** Proof: take a **weak solution** `f`
  of `D` (Lemma 20.5: a smooth, non-holomorphic function with `(1/2πi)∬_X (df/f)∧ω = ∫_c ω`,
  built by hand on coordinate disks + Stokes); the hypothesis makes `∬ (d''f/f)∧ω = 0 ∀ω`; by the
  **Dolbeault/`∂̄`-solvability `Forster 19.10`** there is `g` with `d''g = d''f/f`; then `F := e^{-g}f`
  is a genuine *meromorphic* solution (`d''F = 0`). **[BOOK]**

> **The trap (must flag):** The repo needs **sufficiency**, the harder half. Unwinding §1.1,
> `abelJacobi(P−Q)=0` means `∫_c ω ∈ Per`, i.e. (after correcting the chain by a cycle) Abel's
> condition `∫_{c'} ω = 0 ∀ω` holds. To reach a contradiction one must conclude `P−Q` is principal —
> that is the **sufficiency** direction 20.7a, which **constructs `f`** and is the part that needs
> `∂̄`-solvability (Forster 19.10/19.12), **not** the Trace. The Trace (necessity) alone does *not*
> close the goal. Any claim that "the repo's trace machinery discharges Abel" is **false** for this
> direction. **[VERIFIED by tracing the logic]**

Cost of Route A from scratch: Lemma 20.5 (weak solution of a divisor on the manifold — coordinate-disk
bump construction + manifold Stokes, which the repo only has in the *box/cut* setting) +
`∂̄`-solvability `Forster 19.10` (a Hodge/elliptic-PDE result Mathlib **completely lacks**). This is
**larger** than #7 and has **no Mathlib scaffolding**. Not recommended as a from-scratch target.

### 2.2 Route B — Kleinerman/Griffiths–Harris (third-kind differentials + reciprocity).

The standard textbook proof (Kleinerman §4, read in full this session; Griffiths–Harris Ch.2 "Abel's
theorem"). Engine: **differentials of the third kind** `ω_{PQ}` (meromorphic 1-forms with simple
poles at `P,Q`, residues `±1`, normalized `∫_{aᵢ} ω_{PQ}=0`) + the **Reciprocity Law**
`∫_{bₖ} ω_{PQ} = 2πi ∫_Q^P ω_k` (Riemann's *third* bilinear relation, between first- and third-kind
differentials). Then `µ(D)=0 ⟺ D principal` falls out by writing `df/f = ∑ω_{pₖqₖ} + ∑tᵢωᵢ` and
chasing periods around `aₖ,bₖ`. **[BOOK, Kleinerman pp.4–6]**

- **Pro:** the reciprocity law is *morally identical* to the boundary-word identities the repo's
  `CutSurface` already encodes (R1/R2 are the *first/second* bilinear relations; the reciprocity law
  is the *third*, same cut-surface + Green proof). The repo's `EdgeChangeOfVariables`,
  `boundaryForm`, `rectBoundaryIntegral`, `GreenPositivity` are the right tools and a reciprocity
  lemma would slot beside `cutSurface_R1`.
- **Con:** **existence of `ω_{PQ}` needs Riemann–Roch** (Kleinerman's Lemma 4.1 is a direct
  `h⁰(Ω(p+q)) = g+1` Riemann–Roch+Serre-duality computation), and Mathlib has **no Riemann–Roch**
  (§4). It also needs **sum-of-residues = 0** on a compact RS (Mathlib lacks it, §3) and the
  third-kind reciprocity (new). Net: also a multi-thousand-LoC build, gated on RR.

### 2.3 Verdict on the proof

Both honest from-scratch routes are **larger and less scaffolded than #7**, and each is gated on a
named Mathlib-absent theorem (`∂̄`-solvability for A; Riemann–Roch for B). **The pragmatic
recommendation is to isolate #3 as an input** (§5/§7). If forced to prove, **Route A is the
repo-native one** (reuses Trace) but you still owe the weak-solution + `∂̄` step; **Route B is the one
whose hard input (Riemann–Roch) is the most reusable** (it would also discharge #1
`genus_eq_zero_iff_homeo` and the `FiniteDimensional Ω(X)` / `genus = topological genus` content). If
the project ever invests in **one** big missing theorem, **Riemann–Roch is the highest-leverage
choice** because it unlocks #1, #3 (Route B), and the genus comparison simultaneously.

---

## 3. Mathlib inventory (what exists vs. what's missing)

### 3.1 HAVE (verified this session)

| Capability | Mathlib name | Notes |
|---|---|---|
| Meromorphic order at a point | `meromorphicOrderAt`, `meromorphicOrderAt_comp_of_deriv_ne_zero` | **planar `𝕜→E` only**; repo lifts to manifolds in `Abel.lean`. **[VERIFIED]** |
| Divisor of a meromorphic fn | `MeromorphicOn.divisor : (𝕜→E) → Set 𝕜 → locallyFinsuppWithin U ℤ` | **planar only**; `divisor_mul`, `divisor_prod`, `divisor_inv`, `divisor_zpow`. **[VERIFIED, loogle]** |
| `div(fg)=div f+div g`, `div(1/f)=−div f` | `MeromorphicOn.divisor_mul/_inv/_prod` | the algebra of `div`, planar. **[VERIFIED]** |
| Factorized rationals (build `f` from a divisor) | `MeromorphicOn.extract_zeros_poles`, `MeromorphicNFAt.…factorizedRational` | **planar**; "given a finite divisor on `ℂ`, there is a meromorphic fn with that divisor". Not on a compact RS. **[VERIFIED]** |
| Single-residue Cauchy formula | `Complex.circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable_of_tendsto` → `2πi • y` | the *building block* of a residue theorem, **not** the residue theorem. **[VERIFIED, leansearch]** |
| Box Cauchy / rectangle | `Complex.integral_boundary_rect_eq_zero_of_differentiableOn` | used by `CutSurface`. **[VERIFIED]** |
| Liouville on compact manifold | `MDifferentiable.apply_eq_of_compactSpace`, `…exists_eq_const_of_compactSpace` (`Geometry/Manifold/Complex.lean`) | **holomorphic on compact connected ⟹ constant.** Key for "no non-constant holomorphic fn", and for degree-1 ⟹ iso. **[VERIFIED]** |
| Max modulus on manifolds | `Complex.norm_eventually_eq_of_mdifferentiableAt_of_isLocalMax`, `eqOn_of_isPreconnected_of_isMaxOn_norm` | same file. **[VERIFIED]** |
| Elliptic-curve group law = ideal class group | `WeierstrassCurve.Affine.Point`, `ClassGroup.mk`, `…Point.add` ↔ `ClassGroup` | **genus-1 Abel, but for plane curves over a field — scheme/ideal-theoretic, NOT transferable** to the analytic manifold `X`. Different category. **[VERIFIED]** |
| Function field of a scheme | `AlgebraicGeometry.FunctionField`, `NumberTheory.FunctionField` | abstract; no divisor-class/RR/Abel content. **[VERIFIED]** |
| ℤ-lattice → torus/discrete | `ZSpan.instDiscreteTopology`, `instIsZLatticeRealSpan` | already used for #7. **[VERIFIED, repo]** |

### 3.2 MISSING (would need building / isolating)

- **Residue theorem / argument principle on a compact RS** — `∮ df/f = 2πi(#zeros − #poles)`, and
  **sum of residues of a meromorphic 1-form = 0**. *No* `residue` anywhere in
  `Analysis/Complex/CauchyIntegral.lean`; *no* `ArgumentPrinciple`. **[VERIFIED — grep empty]**
- **`deg(div f) = 0`** on a compact RS (every principal divisor has degree 0). The repo deleted its
  own `deg_div` stub (it was a dead leaf); Mathlib has no manifold version. **[VERIFIED, STATUS.md]**
- **Differentials of the third kind / second kind**, their existence and normalization. Absent.
- **The Riemann reciprocity law** (first–third bilinear relation). Absent (repo has first/second
  relations only, via `CutSurface`). 
- **Weak solution of a divisor** (Forster 20.5) and **`∂̄`-solvability `d''g = α`** (Forster 19.10/12,
  i.e. `H¹(X,O)` / Dolbeault). Absent — this is the same Hodge/`∂̄` gap flagged for #7. **[VERIFIED]**
- **Meromorphic functions / divisors as a manifold-level theory.** The repo builds its own
  (`IsMeromorphic`, `MeromorphicFunction`, `Divisor := X →₀ ℤ`, `MeromorphicFunction.div` via
  `orderLocallyFinsupp`) — Mathlib has none of it for manifolds. **[VERIFIED, `Abel.lean`]**
- **`ℙ¹` as a complex manifold / Riemann sphere**, `Ω(ℙ¹) = 0`, degree-1-cover ⟹ biholomorphism.
  Absent (also blocks #1). **[VERIFIED, `Genus.lean` docstring + grep]**
- **Riemann–Roch** in any form (curves, function fields, analytic). Absent. **[VERIFIED, §4]**

---

## 4. Riemann–Roch in Mathlib

**There is no Riemann–Roch in the pinned Mathlib (`8e3c989`), in any guise.** **[VERIFIED]**

- `find … -iname '*RiemannRoch*'` → empty; `grep -rln 'RiemannRoch'` over all of `Mathlib/` → empty.
- The closest structurally-related result is **`WeierstrassCurve.Affine.Point` ≅ `ClassGroup`**
  (`AlgebraicGeometry/EllipticCurve/Affine/Point.lean`): the group law on a Weierstrass curve over a
  field is proven isomorphic to the degree-0 ideal class group, via the degree-of-a-norm computation
  `degree_norm_smul_basis`. This is *genus-1 Abel for plane curves over a field*, but it is
  **algebraic/scheme-theoretic** and does not connect to the analytic `periodVec`/`Jac` torus used
  here. Not reusable. **[VERIFIED]**
- Community status **[BELIEVED, not re-verified this session]**: Riemann–Roch for curves has been a
  long-standing "wanted" item; there is ongoing work on algebraic-geometry foundations (schemes,
  divisors on schemes, coherent cohomology) but, as of this pin, **no merged RR and no
  curve-divisor-class/`Pic` API** that a Lean proof here could call. Treat "RR exists in Mathlib" as
  **false** for planning.

**Does the Abel path need RR?**
- **Route A (Forster/Trace):** *No RR.* Needs `∂̄`-solvability instead. The **necessity** half needs
  only Trace + `Ω(ℙ¹)=0` (no RR). The **sufficiency** half (what the repo needs) needs the
  weak-solution + `∂̄` step (no RR, but a different Hodge gap).
- **Route B (third-kind/reciprocity):** *Yes, RR* — to prove existence of `ω_{PQ}` (Kleinerman
  Lemma 4.1). 
- **Two-point-specific shortcut:** the *only* place the repo strictly needs is "`µ(P−Q)=0 ⟹ False`".
  As shown in §2.1 this still needs sufficiency (construct `f`). RR is **avoidable** (Route A) but the
  `∂̄` gap is not. **There is no RR-free *and* Hodge-free elementary proof of this statement** — both
  classical routes spend exactly one Mathlib-absent analytic theorem. **[VERIFIED by exhausting both
  textbook proofs in the repo's own references.]**

---

## 5. Keystone decomposition + LoC estimate

Mirroring the period-lattice note's "~4 keystones with LoC". I give the decomposition for the
**recommended isolate-and-derive** plan first (cheap, honest), then a from-scratch estimate.

### 5.1 Recommended: isolate Abel, derive the two-point non-vanishing (≈ 150–400 LoC)

Take **one** isolated input — the *existence half* of Abel for a two-point kernel — and derive the
target. This matches how the repo isolates `exists_cutSurface`, `exists_canonicalDissection`,
`MonodromyLiftFamily`.

1. **`exists_meromorphic_of_abelJacobi_zero` (ISOLATED, the Abel input).**
   `abelJacobi(P−Q)=0 → ∃ f : MeromorphicFunction X, f.div = twoPointDivisor X P Q`. This is Abel
   sufficiency 20.7a specialized to two points. **~0 LoC** (it is the `sorry`/axiom).
2. **`degree_one_map_of_simple_zero_pole`** — from `f.div = P − Q` (`P≠Q`), `f` (as `X→ℙ¹`, or via
   the repo's `ContMDiff.degree`) has degree 1. Uses the repo's already-built degree/fibre-card layer
   (`Discharge/Manifold`, `degreeFiber`, `ContMDiff.degree`). **~150–300 LoC** (the bridge from
   `div f = P−Q` to `ContMDiff.degree f = 1`; the fibre over a generic value is a single simple
   preimage). *Risk:* needs a `ℙ¹` target or an internal "degree of a meromorphic function" — the repo
   has cover-degree for `X→Y` between surfaces, not `X→ℙ¹` yet; may need a small `ℙ¹` shim.
3. **`degree_one ⟹ injective ⟹ genus 0`** — degree-1 holomorphic ⟹ bijective ⟹ biholomorphism
   (Liouville/open-mapping; `MDifferentiable.exists_eq_const_of_compactSpace` is available) ⟹
   `genus X = genus(ℙ¹) = 0`, contradicting `0 < genus X`. **~100–200 LoC** *if* a `ℙ¹`/`genus ℙ¹=0`
   fact is available; **blocked** otherwise (shares the `ℙ¹` gap with #1).

   **Cheaper alternative for step 3 avoiding `ℙ¹`:** a degree-1 cover `f : X → Y` of compact RS is a
   biholomorphism, so `genus X = genus Y`. If `f.div = P−Q` is read as `f : X → ℙ¹` we still need
   `genus ℙ¹ = 0`. The genuinely `ℙ¹`-free contradiction: "a non-constant meromorphic function with a
   *single simple pole* exists ⟹ `g = 0`" is itself essentially `genus_eq_zero_iff_homeo`/Riemann–Roch
   territory — so step 3 cannot be made both cheap and `ℙ¹`-free. Recommend pulling in a minimal `ℙ¹`
   manifold (also needed by #1) rather than re-deriving.

**Total recommended:** **~250–500 LoC of derivation on top of one isolated Abel axiom**, *provided*
a small `ℙ¹` complex-manifold shim (`genus ℙ¹ = 0`, `Ω(ℙ¹)=0`) is admitted (shared with #1). Without
the `ℙ¹` shim, steps 2–3 stall and the cheapest honest move is to isolate the *whole* statement
`abelJacobi_twoPoint_ne_zero` (status quo) — **0 LoC, 1 sorry**.

### 5.2 From-scratch (Route A, Forster) — for scale only

| Keystone | Content | Est. LoC | Mathlib scaffold? |
|---|---|---|---|
| `weakSolution_of_divisor` | Forster 20.5: smooth `f` with prescribed `div`, `(1/2πi)∬(df/f)∧ω=∫_c ω` | **800–1500** | partial (manifold Stokes only in box form) |
| `dbar_solvable` (`d''g=α`) | Forster 19.10/12 Dolbeault `H¹(X,O)` / elliptic `∂̄` | **1500–3000+** | **none** (same Hodge gap as #7's Hodge route) |
| `abel_sufficiency` | assemble `F=e^{-g}f` meromorphic, `(F)=D` | **300–600** | — |
| two-point endgame | §5.1 steps 2–3 | **250–500** | partial (repo degree layer) |
| **Total** | | **~3k–6k+** | mostly absent |

This is **strictly more** than #7 (#7 ≈ 2–4k with heavy Mathlib box-Green scaffolding; here the
`∂̄` keystone has *no* scaffolding). **Do not pursue from scratch unless the `∂̄`/Hodge layer is being
built anyway for #7's Hodge variant.**

### 5.3 What to isolate vs. prove

- **Isolate** (repo-style): the Abel input `exists_meromorphic_of_abelJacobi_zero`. It is a *named
  classical theorem absent from Mathlib*, exactly the category the repo already isolates.
- **Prove** (tractable, reuses existing layers): the two-point endgame (deg-1 ⟹ iso ⟹ `g=0`), *if*
  the `ℙ¹` shim is admitted. The repo's `Discharge/Manifold` degree/Hurwitz code is the asset here.
- **Do not** attempt `weakSolution_of_divisor` or `dbar_solvable` from scratch in isolation — wrong
  cost/benefit.

---

## 6. Connection to #7 (the "meet in the middle" — answered: NO)

**Question:** once #7 gives "period lattice is a full-rank ℝ-lattice", does `abelJacobi_twoPoint_ne_zero`
follow cheaply?

**Answer: No. #3 and #7 are logically independent; #7 does not discharge #3, even partially.**
Reasons, in increasing depth:

1. **Type-level:** #7's output is `∃ basis b, truePeriodLattice X = span ℤ (range b)` — a statement
   about the lattice `Per` *as a subset of `ℂ^g`*. #3 is a statement about a *specific point*
   `periodVec(sp P Q) ∈ ℂ^g` and whether it lies in `Per`. Knowing `Per` is a nice full-rank lattice
   tells you it is discrete and co-compact; it tells you **nothing** about which non-lattice-looking
   vectors avoid it. A full-rank lattice has points everywhere (it spans `ℝ^{2g}` over `ℝ`); the
   integral `∫_Q^P ω⃗` *could a priori* be one of them. Ruling that out **is** Abel's theorem.
   **[VERIFIED by structural reading of `Dissection.lean` + `Abel.lean`]**

2. **Sanity check via genus 1.** For `g=1`, `Jac = ℂ/Λ` with `Λ = ℤ·1 + ℤ·τ` full-rank (that's #7).
   `abelJacobi(P−Q)=0` ⟺ `∫_Q^P ω ∈ Λ`. Full-rank-ness of `Λ` is *given* and yet the non-vanishing
   `∫_Q^P ω ∉ Λ` for `P≠Q` is a *separate* fact — it is exactly the injectivity of `X ↪ ℂ/Λ`
   (Forster **21.10**), which is *not* implied by `Λ` being a lattice. (Indeed for the wrong "fake"
   period data one could have a full-rank lattice yet a non-injective map.) So even in the simplest
   case #7 ⊬ #3. **[BOOK + VERIFIED]**

3. **Different bilinear relations.** #7's `CutSurface` encodes the **first and second** Riemann
   bilinear relations (R1 `AᵀB=BᵀA`; R2 positivity `i(AᵀB̄−BᵀĀ)≻0`) — relations *among the period
   matrix entries*. Abel's proof (Route B) needs the **third** relation, the **reciprocity law**
   `∫_{bₖ}ω_{PQ}=2πi∫_Q^P ω_k`, which couples first-kind periods to a **third-kind differential** that
   #7 never constructs. The cut-surface is the *right machine* to also prove reciprocity, but it is
   **additional work**, not a byproduct of R1/R2. **[VERIFIED: `CutSurfaceRelations.lean` proves only
   R1/R2.]**

**Where #7 *does* help (the honest "partial credit"):** the `CutSurface`/`EdgeChangeOfVariables`/
`boundaryForm`/`GreenPositivity` toolkit is exactly what a **reciprocity-law lemma** (Route B's core)
would be built on. So #7 lowers the marginal cost of Route B's reciprocity step — but Route B is still
gated on **Riemann–Roch** (existence of `ω_{PQ}`), which #7 does nothing for. **Net: #7 shares
*infrastructure* with a Route-B attack on #3, but does not *discharge* any logical part of #3.**

**Conversely**, the asset that *does* transfer is the **Trace layer** (`traceForm`, `pushforward`,
`Discharge/Manifold` degree) — but that powers Abel **necessity**, and the repo needs **sufficiency**
(§2.1). So even the strongest existing asset only covers the half the repo doesn't need.

---

## 7. Documentation correction (cite the right theorem)

The current `Abel.lean` docstrings and `docs/REFERENCES.md` cite this leaf as **"Forster §21.5 /
Miranda V§2.8, Abel + Riemann–Hurwitz"** and describe the proof as "principal ⟹ degree-1 map ⟹
Riemann–Hurwitz ⟹ genus 0". After reading the actual Forster PDF:

- **§20 is "Abel's Theorem"; §21 is "The Jacobi Inversion Problem".** The *injectivity* the repo
  needs is **Forster Thm 21.7** (p.171, `j: Pic⁰ ↪ Jac`), whose kernel input is **Abel 20.7**
  (p.163). The genus-1 endpoint is **Thm 21.10** (p.172). `REFERENCES.md`'s row
  "`ofCurve_inj` (Abel's theorem) | Forster §21" should read **§20 (Abel) + §21.7 (injectivity)**.
- The repo's "degree-1 ⟹ Riemann–Hurwitz ⟹ genus 0" is the *endgame* (my §5.1 steps 2–3), which is
  correct **but** it is downstream of the hard part: you first need **Abel sufficiency 20.7a** to get
  `f` at all. "Riemann–Hurwitz" overstates the need — degree-1-cover-is-iso needs only
  Liouville/open-mapping (`MDifferentiable.exists_eq_const_of_compactSpace`, **available**), not the
  full Hurwitz formula. The genuine missing engine is **`∂̄`-solvability (Forster 19.10/12)**, which
  the docstrings do not mention. Recommend updating the comment to name `∂̄`/weak-solutions (Route A)
  or Riemann–Roch (Route B) as the real input, and Liouville (not Hurwitz) for the endgame.

---

## 8. Sources (verified this session)

**Primary:**
- **Otto Forster, *Lectures on Riemann Surfaces* (GTM 81)** — `§20 Abel's Theorem` pp.159–164
  (20.1 functions w/ prescribed divisors; 20.3 the `∬ df/f ∧ dg` lemma; 20.5 weak solutions; **20.7
  Abel's Theorem** w/ Trace-based necessity proof p.164); `§21 Jacobi Inversion` pp.165–172 (21.2–21.4
  period lattice; **21.7 `j: Pic⁰(X) ↪ Jac(X)` injective**, p.171; 21.9 surjectivity via **RR 16.9**;
  **21.10 `J:X→Jac` iso for `g=1`**, p.172). The Forster PDF is a **scanned image** (no text layer —
  read via the visual PDF reader, pages 165–178 of the file = book pp.159–172). **[BOOK]**
- **Griffiths–Harris, *Principles of Algebraic Geometry*** (repo root PDF) — Ch.2, "Abel's theorem",
  third-kind differentials + reciprocity (Route B). **[BOOK, referenced]**

**Secondary / cross-check (fetched + text-extracted this session):**
- **Seth Kleinerman, *The Jacobian, the Abel–Jacobi Map, and Abel's Theorem*** —
  https://wstein.org/projects/kleinerman_99paper.pdf — §3 AJ map, §4 **Abel** (Lemma 4.1 third-kind
  via **Riemann–Roch+Serre duality**; Lemma 4.2 **Reciprocity Law**; Thm 4.3 proof pp.4–6),
  §5 Jacobi inversion. The clean modern writeup of Route B. **[BOOK, full text read]**
- **Donu Arapura, *The Jacobian of a Riemann Surface*** —
  https://www.math.purdue.edu/~arapura/preprints/jacobian.pdf — **cohomological** route (de Rham +
  Dolbeault `H¹(X,O)`; "Abel's theorem is a tautology" given the `H¹` definition, p.313). Confirms the
  sheaf-cohomology reformulation this project must *avoid*; useful only as the contrast case. **[BOOK]**
- Wikipedia *Abel–Jacobi map* (injective iff `g≥1`); Tao 246C notes (modern RR). **[BELIEVED]**

**Mathlib (verified by source/loogle/leansearch at pin `8e3c989`):**
- `Mathlib/Analysis/Meromorphic/Divisor.lean` — `MeromorphicOn.divisor`, `divisor_mul/_inv/_prod/_zpow`
  (planar). `FactorizedRational.lean` — `extract_zeros_poles` (build `f` from a divisor, **planar**).
- `Mathlib/Analysis/Complex/CauchyIntegral.lean` — `circleIntegral_sub_center_inv_smul_…_tendsto`
  (single residue `→2πi•y`), `integral_boundary_rect_eq_zero_of_differentiableOn` (box Cauchy).
  **No `residue`, no argument principle.**
- `Mathlib/Geometry/Manifold/Complex.lean` — `MDifferentiable.exists_eq_const_of_compactSpace`,
  `apply_eq_of_compactSpace` (**Liouville on compact manifolds**), max-modulus on manifolds.
- `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean` — `WeierstrassCurve.Affine.Point` ≅
  `ClassGroup` (genus-1 Abel, **algebraic, not transferable**).
- **No Riemann–Roch anywhere** (`grep RiemannRoch` empty). No `ℙ¹`/Riemann-sphere manifold, no Hodge/
  `∂̄`-solvability, no manifold residue/argument-principle, no manifold `deg(div f)=0`.

**Repo (read this session):** `Jacobians/Abel.lean` (target + `abelJacobi`, `ofCurve` connection),
`Jacobians/PeriodLattice.lean`, `Jacobians.lean` (`ofCurve`, `ofCurve_inj`), `Jacobians/Genus.lean`,
`Jacobians/Dissection.lean` + `CutSurfaceRelations.lean` + `BoundaryWordR2.lean` (the #7 machinery),
`Jacobians/TraceForm.lean` (`traceForm`), `docs/STATUS.md`, `docs/period_realbasis_plan.md`.
