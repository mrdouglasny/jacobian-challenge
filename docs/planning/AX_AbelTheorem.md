# `AX_AbelTheorem` — discharge recipe

> ## ⟳ Substrate refresh — 2026-06-07 (read before the 2026-06-03 recipe below)
>
> This is the **deepest open node** of the Abel–Jacobi cluster and the chosen
> "deepest part" target. Four things changed since the 2026-06-03 recipe:
>
> 1. **Some "Blocked by" entries are resolved.** `PrincipalDivisors` now has a
>    real body (`= divHom.range`, G3 workstream — no longer "no body"), and a
>    meromorphic-function theory exists: `MeromorphicFunctionField.Rep X` with
>    `orderAt`, `divisor`, `orderFinsupp`, and locally-finite / finite order
>    support (`orderCoeff_locallyFiniteSupport`, `orderSupport_finite`). So the
>    `⊇` direction's statement "`div f = D` ⟺ `D ∈ PrincipalDivisors X`" is now
>    *expressible* against real defs, not stubs. `AX_BranchLocus` is now a
>    **theorem** too.
>
> 2. **`AX_ofCurve_inj` was discharged (2026-06-05) by a DIFFERENT route.** The
>    2026-06-03 cross-plan note claimed this Forster residue+period route would
>    be "the unified Abel–Jacobi infrastructure consumed by `AX_ofCurve_inj` as
>    well." That is now **superseded**: `ofCurve_inj` was instead closed via the
>    homotopy-invariance / `developingValue` / `loopIntegralToH1` route (see
>    `Elliptic/OfCurveInj.lean` + the HI workstream), *without* building the
>    residue theorem. Lesson for this plan: the HI machinery is a real, landed
>    asset — the `⊇` direction's period-comparison (recipe step 1c) may be
>    reachable through `loopIntegralToH1` + `canonicalArcIntegral_homotopy_invariant`
>    rather than a from-scratch contour-integral residue theorem.
>
> 3. **The residue-theorem route decision is RESOLVED (2026-06-07): bypass it.**
>    Gemini deep-think + Mathlib-name verification concluded the residue theorem
>    is a *trap* for `⊇` — fundamental-polygon and partition-of-unity both need
>    3000+ LOC of nonexistent manifold-Stokes API, and the `df/f`
>    argument-principle bootstrap only reaches integer residues. The recommended
>    `⊇` route instead proves **the Jacobi map `Φ(y) = AJ(f⁻¹(y))` is constant on
>    the rational pencil `ℙ¹`** (holomorphic + bounded ⇒ Liouville ⇒ constant ⇒
>    `AJ(zeros)=AJ(poles)`), reusing `weightedFiberConservation` and dodging
>    residues entirely because the `jacobianBasis` forms are *holomorphic*. Full
>    verified route + ~800–1200 LOC 4-file decomposition:
>    [`ABEL_SUPSET_LIOUVILLE_ROUTE.md`](ABEL_SUPSET_LIOUVILLE_ROUTE.md). The
>    Forster residue + period-normalization `⊇` recipe below is **superseded** by
>    that route (kept for historical record). The general residue theorem is
>    *deferred*, only re-opening if Serre duality needs it (then the
>    picard-lefschetz contour-integration repo is the local-pieces substitute).
>
> 4. **The `⊆` direction (Jacobi inversion) is still genuinely blocked.** It
>    consumes `AX_RiemannRoch` + `AX_SerreDuality` (both still axioms) to build
>    the third-kind differential, plus `AX_RiemannBilinear`. Do **not** attempt
>    `⊆` before those land. The `⊇` direction (principal ⇒ kernel), by contrast,
>    needs only the residue theorem + `AX_RiemannBilinear` reciprocity and is the
>    right first half to target.
>
> **Net:** terminal node, still multi-month, but the residue-theorem route is
> the live decision and the `⊇` half is the tractable first milestone. The LOC
> estimate below is pending the route decision in (3).

## Split + route map (2026-06-07)

`AX_AbelTheorem : ker(abelJacobiDiv X) ⊓ (deg X).ker = PrincipalDivisors X` is a
biconditional. **Proposal: split it into two named lemmas** so the dependency
graph is honest about which half the challenge needs:

- **⊇ (easy)** `principal ⇒ kernel` — `PrincipalDivisors ⊆ ker ⊓ deg-0`.
  Route: [`ABEL_SUPSET_LIOUVILLE_ROUTE.md`](ABEL_SUPSET_LIOUVILLE_ROUTE.md)
  (Jacobi-map-constant-on-ℙ¹ via Liouville; ~800–1200 LOC; **no Stokes, no RR/Serre**).
- **⊆ (hard)** `kernel ⇒ principal` (Jacobi inversion) — `ker ⊓ deg-0 ⊆ PrincipalDivisors`.
  **This is the half the challenge's `ofCurve_inj` actually consumes**
  (`OfCurveInjective.lean:34`). Two routes:
  - Route A (Forster): [`ABEL_SUBSET_FORSTER_ROUTE.md`](ABEL_SUBSET_FORSTER_ROUTE.md)
    — third-kind differential via RR+Serre; gated on the sheaf-cohomology cluster.
  - Route B (Mumford theta): [`ABEL_SUBSET_MUMFORD_THETA_ROUTE.md`](ABEL_SUBSET_MUMFORD_THETA_ROUTE.md)
    — Riemann theta + theta divisor; **independent of RR/Serre**, concrete/algebraic;
    **recommended**, with a genus-1 base case via Mathlib `jacobiTheta`.

Why split: `ofCurve_inj` currently depends on the *whole* biconditional axiom, so
the cheap ⊇ Liouville build wouldn't reduce the challenge's axiom load on its own.
Splitting lets `ofCurve_inj` depend only on the ⊆ lemma, makes the hard direction
the visible blocker, and lets ⊇ land independently. Shared foundation for **both**
⊆ routes: `AX_RiemannBilinear` (the A-normalized basis / `τ ∈ Siegel`) +
`AX_AnalyticCycleBasis`. **Under discussion** (governance: splitting a soundness-
adjacent axiom) — see the linked GitHub Discussion before the implementing PR.

**Location:** `Jacobians/Axioms/AbelTheorem.lean:66`
**Route:** genuine-textbook (with substantial `needs-infra` substrate) &nbsp;&nbsp; **Effort:** 8 &nbsp;&nbsp; **Est:** ~9–18 months, ~6000–9000 LOC across new files (manifold-integration + residue infrastructure absolutely dominates; the residue theorem alone is 2000–3500 LOC, not 50; the Abel-theorem assembly proper is the smaller ~1000–1500 LOC tail)
**Blocked by:** `abelJacobiDiv` (`Jacobians/Axioms/AbelTheorem.lean:60`), `PrincipalDivisors` (`Jacobians/RiemannSurface/LineBundle.lean:70`), `Divisor.deg` (`Jacobians/RiemannSurface/LineBundle.lean:63`), the sheaf-cohomology layer (`LineBundle`, `H0`, `H1` at `Jacobians/RiemannSurface/LineBundle.lean:77,85,104`), and downstream-axiom prerequisites `AX_RiemannRoch` (`Jacobians/Axioms/RiemannRoch.lean:59`), `AX_SerreDuality` (`Jacobians/Axioms/SerreDuality.lean:54`), `AX_RiemannBilinear` (`Jacobians/Axioms/RiemannBilinear.lean:69`), `AX_AnalyticCycleBasis` (`Jacobians/Axioms/AnalyticCycleBasis.lean:257`), `AX_PeriodLattice` (`Jacobians/Axioms/PeriodLattice.lean:92`).

**Statement (verbatim):**
```lean
/-- **Axiom (Abel's theorem).** The kernel of the Abel-Jacobi map on
divisors is exactly the subgroup of principal divisors. -/
axiom AX_AbelTheorem {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] :
    (abelJacobiDiv X).ker = PrincipalDivisors X
```

**Why it's an axiom right now:** Abel's theorem is the heart of 19th-century algebraic geometry and is genuinely a substantial theorem in both directions. The `⊇` direction (principal ⇒ kernel) requires the **residue theorem for meromorphic 1-forms on a compact Riemann surface** plus the **reciprocity law** between differentials of the first and third kind (Riemann's bilinear relations). The `⊆` direction (kernel ⇒ principal — the *Jacobi inversion* problem) requires either a delicate construction of a normalized differential of the third kind (Forster route) or the theta-divisor theorem (Mumford route). The project currently has no meromorphic-function theory on compact Riemann surfaces, no `PrincipalDivisors` body, no residue calculus in the manifold setting, and Mathlib itself lacks integration on manifolds with boundary, oriented cycle integration, and the limit theorems for shrinking tubular neighborhoods around poles. This axiom is therefore the *terminal* node of the Abel-Jacobi dependency chain in the ROADMAP (see lines 146–152).

**Proof recipe**

We outline the **Forster residue route** (Otto Forster, *Lectures on Riemann Surfaces*, §21, "Abel's Theorem"). The Mumford theta route is sketched as an alternative at the end.

Notation: write `g := genus X`. For a divisor `D = ∑ n_i P_i` with `Divisor.deg X D = 0` (`Jacobians/RiemannSurface/LineBundle.lean:63`), write `u(D) := abelJacobiDiv X D ∈ Jacobian X`. A symplectic homology basis `{a_1,…,a_g, b_1,…,b_g}` of `H_1(X,ℤ)` is supplied by `AX_AnalyticCycleBasis` (`Jacobians/Axioms/AnalyticCycleBasis.lean:257`).

1. **⊇ direction (principal ⇒ kernel).** Let `f : X → ℂ ∪ {∞}` be a nonzero meromorphic function with `div f = D`.
   * Step (a): `dlog f = df/f` is a meromorphic 1-form on `X` of the third kind whose residue at any point `P` is `ord_P(f)`.
   * Step (b): for each cycle `γ ∈ {a_j, b_j}` (with `γ` deformed to avoid `supp(div f)`), apply the **residue theorem on `X ∖ supp(div f)`**. This gives `∮_γ dlog f ∈ 2πi · ℤ` because each enclosed residue is an integer.
   * Step (c): to conclude `u(div f) = 0` in `Jacobian X = ℂ^g / Λ` we must compare *period integrals of holomorphic 1-forms over the chain from `P₀` to the divisor points* with the *integrals of `dlog f` over the homology basis*. This comparison is precisely the **reciprocity law for differentials of the first and third kind**, which is one face of Riemann's bilinear relations (`AX_RiemannBilinear`, `Jacobians/Axioms/RiemannBilinear.lean:69`). Concretely, for each holomorphic 1-form `ω_j` in the symplectic-dual basis (cf. `periodMap` at `Jacobians/RiemannSurface/Periods.lean:39` and `periodMapInBasis` at `Jacobians/Axioms/PeriodLattice.lean:53`), Riemann reciprocity yields `∑_i n_i ∫_{P₀}^{P_i} ω_j ≡ (1/(2πi)) · (cross-term involving periods of dlog f) (mod Λ)`. Because the periods of `dlog f` lie in `2πi · ℤ`, the right-hand side lies in the period lattice `Λ = periodLatticeInBasis` (`Jacobians/Axioms/PeriodLattice.lean:63`), so `u(div f) = 0`. Forster §21 Lemma 21.4 + Theorem 21.5; Griffiths–Harris p. 233 (Reciprocity for differentials of first and third kind).

2. **⊆ direction, Step 1 (set-up for Jacobi inversion).** Suppose `D` is degree-0 with `u(D) = 0`. Decompose `D = D⁺ − D⁻` with `Divisor.deg X D⁺ = Divisor.deg X D⁻ = m`. Goal: produce a meromorphic `f` with `div f = D`. Equivalently, find a meromorphic differential `ω_D` *of the third kind* — simple poles only, residue `+1` at each point of `D⁺`, residue `−1` at each point of `D⁻` (counted with multiplicity) — whose periods lie in `2πi · ℤ` over **every** cycle of the homology basis, so that `exp(∫ ω_D)` is single-valued. Forster §21 Theorem 21.6.

3. **⊆ direction, Step 2 (existence of a third-kind differential `ω_D`).** Apply Riemann–Roch (`AX_RiemannRoch`, `Jacobians/Axioms/RiemannRoch.lean:59`) and Serre duality (`AX_SerreDuality`, `Jacobians/Axioms/SerreDuality.lean:54`) to the line bundle `𝒪(D⁺ + D⁻)` twisted by the canonical bundle `K_X` (`Jacobians/RiemannSurface/LineBundle.lean:123`) to produce a meromorphic 1-form `ω_D` with the required residue pattern. At this stage `ω_D` is determined only up to addition of a holomorphic 1-form. Forster §21.7; Mumford Vol I §II.3 Prop 3.4.

4. **⊆ direction, Step 3 (period adjustment via A-period normalization and Riemann reciprocity).** Let `{ω_1^{hol}, …, ω_g^{hol}}` be a basis of `H⁰(X, Ω¹)` *normalized to the A-cycles*, i.e. `∮_{a_i} ω_j^{hol} = δ_{ij}` (this normalization is part of `AX_RiemannBilinear`, `Jacobians/Axioms/RiemannBilinear.lean:77`; note the integral against `αEmbed` evaluates to `δ_{ij}`). Then for *any* third-kind form `ω_D` from Step 3 we can subtract `∑_j (∮_{a_j} ω_D) · ω_j^{hol}` to produce a corrected form

   `ω̃_D := ω_D − ∑_j (∮_{a_j} ω_D) · ω_j^{hol}`

   with **all A-periods zero**: `∮_{a_j} ω̃_D = 0` for every `j`. Now apply Riemann's bilinear-reciprocity identity (`AX_RiemannBilinear`, `Jacobians/Axioms/RiemannBilinear.lean:69`, second-and-third-kind variant) to express the B-periods `∮_{b_j} ω̃_D` in terms of `∑_i n_i ∫_{P₀}^{P_i} ω_j^{hol}` — *exactly* the components of `u(D)` modulo `Λ`. The hypothesis `u(D) = 0` says those components lie in the period lattice `Λ = periodLatticeInBasis X x₀ b` (`Jacobians/Axioms/PeriodLattice.lean:63`). Multiplying through by `2πi`, the conclusion is that **every B-period of `ω̃_D` lies in `2πi · ℤ + 2πi · ℤ · τ` ∩ `2πi · ℤ`**, i.e. in `2πi · ℤ`. Combined with the A-periods being zero (hence in `2πi · ℤ`), **all periods of `ω̃_D` lie in `2πi · ℤ`**. Forster §21.8.

   *Mathematical correction (vs. previous draft):* the previous draft said "purely imaginary periods so that `exp` is single-valued" — that is **wrong** (`exp(iπ) = −1`, not `1`). The correct condition is **periods in `2πi · ℤ`**. Likewise the previous draft said "all real periods become integer multiples of `2πi`", which conflated two unrelated notions; the correct procedure is to set **A-periods** (integrals over the `a_j` cycles) to zero by adjustment, then use Riemann reciprocity to force the **B-periods** (over the `b_j` cycles) into `2πi · ℤ` using the hypothesis `u(D) = 0`.

5. **⊆ direction, Step 4 (basepoint selection, with pole avoidance).** We need a basepoint `P₀ ∈ X` for the integral `∫_{P₀}^P ω̃_D`. **`P₀` must be chosen disjoint from `supp(D⁺) ∪ supp(D⁻)`**, because `ω̃_D` has simple poles at exactly those points and `∫_{P₀}^P ω̃_D` would diverge if `P₀` were a pole. Construction:
   * `supp(D)` is finite (divisors have finite support).
   * `X` is compact, connected, and second-countable, hence has uncountably many points (any nonempty open subset of `X` has cardinality `2^{ℵ₀}` because charts are open in `ℂ`).
   * Therefore `X ∖ supp(D)` is nonempty (in fact open and dense), and we may take `P₀ ∈ X ∖ supp(D)` via `Classical.choice` applied to the nonemptiness proof.

   *Mathematical correction (vs. previous draft):* the previous draft picked `P₀` via `Classical.arbitrary X`, which is **mathematically broken** because `Classical.arbitrary` can return any inhabitant — including a point of `supp(D)` — making `f(P₀)` undefined. The fix is to package the basepoint selection as a `Nonempty (X ∖ supp(D⁺) ∪ supp(D⁻))` lemma proved from finiteness of divisor support plus the open-dense argument above, and feed it to `Classical.choice`.

6. **⊆ direction, Step 5 (recover the meromorphic function).** Define `f(P) := exp(∫_{P₀}^P ω̃_D)`. Because **all** periods of `ω̃_D` lie in `2πi · ℤ`, the integral is well-defined modulo `2πi · ℤ`, so `exp` of it is **single-valued** on `X ∖ supp(D)`. Near each pole `P_i ∈ D⁺`, the integral has local expansion `n_i · log(z − z_i) + holomorphic`, hence `f(P) ∼ (z − z_i)^{n_i}`, i.e. `ord_{P_i}(f) = n_i`. Similarly for `D⁻`. Therefore `f` extends meromorphically across `supp(D)` with `div f = D⁺ − D⁻ = D`. Hence `D ∈ PrincipalDivisors X` (`Jacobians/RiemannSurface/LineBundle.lean:70`).

7. **Assemble.** Combine (1) for `⊇` and (2)–(6) for `⊆`. Replace `axiom AX_AbelTheorem` at `Jacobians/Axioms/AbelTheorem.lean:66` with `theorem AX_AbelTheorem` whose body is `AddSubgroup.ext` followed by a `constructor` splitting the iff.

**Gemini critique addressed:**
The following math errors flagged by Gemini 3.1 Pro have been corrected in this revision:
* **"Purely imaginary" → `2πi · ℤ` lattice.** The previous draft said `ω̃_D` should have "purely imaginary periods (so that exp is single-valued)". This is false: `e^{iπ} = −1 ≠ 1`, so purely imaginary periods do not make `exp` single-valued. Step 4 now correctly states the condition: **all periods must lie in `2πi · ℤ`**.
* **"Real periods" → A-periods.** The previous draft spoke of adjusting "real periods" to integer multiples of `2πi`, which is nonsense as stated. The correct procedure is the two-stage **A-period / B-period normalization**: first kill A-periods by subtracting a normalized holomorphic differential (Step 4 first half), then use Riemann reciprocity together with the hypothesis `u(D) = 0` to force the remaining B-periods into `2πi · ℤ` (Step 4 second half). Step 4 now spells this out using the A-cycle normalization from `AX_RiemannBilinear` (`Jacobians/Axioms/RiemannBilinear.lean:77`).
* **Bilinear-relations dependency for Step 1 (`⊇`).** The previous draft hand-waved Step 1(c) as "pairing against `dlog f` modulo the period lattice yields zero". This was incomplete — equating the holomorphic-form integrals over chains from `P₀` to divisor points with the periods of `dlog f` is the **reciprocity law for differentials of the first and third kind**, i.e. Riemann's bilinear identity (`AX_RiemannBilinear`, `Jacobians/Axioms/RiemannBilinear.lean:69`). Step 1(c) now explicitly cites this and the dependency is added to the "Blocked by" line.
* **Basepoint pole avoidance.** The previous draft picked `P₀` via `Classical.arbitrary X`, which can land in `supp(D)`, a pole of `ω̃_D`, making `∫_{P₀}^P ω̃_D` divergent. Step 5 now selects `P₀` from the cofinite open set `X ∖ supp(D)` using a `Nonempty` lemma derived from finiteness of divisor support plus density.
* **Residue-theorem LOC honesty.** The previous draft estimated the residue theorem on a compact Riemann surface as a "50-LOC corollary of Stokes". This is a formalization fantasy: Mathlib has no integration on manifolds with boundary, no orientation-tracked cycle integration, no Stokes for manifolds with boundary on charted spaces, no tubular-neighborhood-shrinking limit theorems around isolated singularities, and no analytic residue calculus (the only `Residue*` files in Mathlib are `AlgebraicGeometry/ResidueField.lean`, which is the algebraic residue field of a local ring — unrelated). A realistic estimate for the residue theorem on a compact Riemann surface, built from scratch, is **2000–3500 LOC** across at least: a `BoundaryStokes.lean` (manifold Stokes with boundary), a `TubularNeighborhood.lean` (shrinking disks around isolated singularities + limit theorem), and `Residues.lean` itself. The headline LOC estimate at the top of this file has been corrected accordingly.

**Next discrete deliverable.** The smallest well-scoped unit that unblocks Step 1 — and gives a real foothold — remains a separate file `Jacobians/RiemannSurface/Residues.lean` exposing
```lean
theorem residue_thm_on_compact_RS
    (ω : MeromorphicOneForm X) :
    ∑ P ∈ supp ω, residue ω P = 0
```
**but** this is now understood as the *capstone* of a multi-month infrastructure project, not a 50-LOC corollary. Realistic decomposition:
1. `Jacobians/RiemannSurface/MeromorphicForms.lean` — define meromorphic 1-forms, local Laurent expansions, residues via small-circle integrals (~600–900 LOC).
2. `Jacobians/RiemannSurface/BoundaryStokes.lean` — Stokes' theorem for 2-forms on a 2-real-dimensional compact manifold with boundary (~800–1200 LOC; Mathlib has only the no-boundary version on closed manifolds and the calculus-style Green's theorem on planar domains).
3. `Jacobians/RiemannSurface/PunctureLimits.lean` — limit theorem `∫_{|z−p|=ε} ω → 2πi · res_p(ω)` as `ε → 0`, plus the version for finite sets of punctures (~400–700 LOC).
4. `Jacobians/RiemannSurface/Residues.lean` — the residue theorem itself, by carving out punctures from a fundamental polygon and applying (2)+(3) (~200–400 LOC for the assembly, **not** 50).
Once these four files land, Step 1 in the recipe above is a genuine corollary, but the total residue infrastructure is `~2000–3200 LOC` — comparable in size to building `AX_RiemannRoch` itself.

**Alternative: Mumford theta route (Mumford Vol I, §II.3.3–II.3.5).** Same `⊇` proof. For `⊆`: construct the Riemann theta function `θ : ℂ^g → ℂ` (Mumford §II.3.3), prove Riemann's theorem identifying the theta divisor with `u(W_{g−1})` for `W_{g−1}` the image of `(g−1)`-fold symmetric products (Mumford §II.3.4), then deduce surjectivity and injectivity of `u : Pic⁰(X) → Jacobian X` simultaneously (Mumford §II.3.5). This route routes through `Jacobians/AbelianVariety/Theta.lean` (scaffolded per the source-file docstring) and through `Jacobians/Axioms/UniversalProperty.lean` (`AX_curve_generates_jacobian`). It is **conceptually cleaner but requires multivariable complex analysis of `θ`** — Mathlib has no theta function yet — and a non-vanishing-locus argument for the theta divisor. Per-route LOC cost is similar or higher; the basepoint-pole issue does *not* arise in this route, but the multivariable holomorphic-function machinery cost is comparable to the residue infrastructure.

**Files touched**
- `Jacobians/Axioms/AbelTheorem.lean` — replace `axiom AX_AbelTheorem` at line 66 with the assembled theorem; also discharge `axiom abelJacobiDiv` at line 60 into a real `def` (or rework its definition to take a non-pole basepoint as an argument).
- `Jacobians/RiemannSurface/MeromorphicForms.lean` — **new file**: meromorphic 1-forms, residues via small-circle integrals, third-kind differentials.
- `Jacobians/RiemannSurface/BoundaryStokes.lean` — **new file**: Stokes' theorem on a 2-real-dimensional compact manifold with boundary.
- `Jacobians/RiemannSurface/PunctureLimits.lean` — **new file**: shrinking-disk limit theorems.
- `Jacobians/RiemannSurface/Residues.lean` — **new file**: residue theorem on a compact Riemann surface (the capstone of the previous three).
- `Jacobians/RiemannSurface/LineBundle.lean` — discharge `PrincipalDivisors` (line 70) into a real `def` once meromorphic-function theory exists; this is a separate planning item (see `PrincipalDivisors.md`).
- Downstream prerequisites that must already be theorems (or remain genuine axioms used as hypotheses): `AX_RiemannRoch` (`Jacobians/Axioms/RiemannRoch.lean:59`), `AX_SerreDuality` (`Jacobians/Axioms/SerreDuality.lean:54`), `AX_RiemannBilinear` (`Jacobians/Axioms/RiemannBilinear.lean:69`), `AX_AnalyticCycleBasis` (`Jacobians/Axioms/AnalyticCycleBasis.lean:257`), `AX_PeriodLattice` (`Jacobians/Axioms/PeriodLattice.lean:92`).

**Acceptance**
- `lake build Jacobians.Axioms.AbelTheorem` succeeds.
- `#print axioms AX_AbelTheorem` no longer lists `AX_AbelTheorem`. (It will still list `AX_RiemannRoch`, `AX_SerreDuality`, `AX_RiemannBilinear`, `AX_AnalyticCycleBasis`, `AX_PeriodLattice`, which are separate genuine-textbook items.)
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1 (or by 2 if `abelJacobiDiv` is dischargeable in the same pass).

**Risk / escalation triggers**
- If building `Jacobians/RiemannSurface/BoundaryStokes.lean` requires changing the `ChartedSpace ℂ X` / `IsManifold 𝓘(ℂ, ℂ) ω X` typeclass surface to add an *analytic-manifold-with-corners* refinement, escalate — this touches every axiom in the project.
- If `AX_RiemannRoch` or `AX_RiemannBilinear` does not land first, **do not attempt Steps 3 or 4**; the `⊆` direction is genuinely blocked. Escalate immediately if scheduling pressure pushes this recipe ahead of either.
- If the cumulative residue-infrastructure LOC overshoots ~3500 within the first 4–6 weeks of implementation work on `BoundaryStokes.lean`, escalate to consider the **Mumford theta route** instead — at that point the multivariable-theta cost may be comparable and the route is conceptually cleaner.

---
**Vetting trail.** Critique: `_vetting/AX_AbelTheorem.md`. Verdict: revise. Revised: 2026-06-03.

**Cross-plan patch (2026-06-03):** Anchored two cross-plan alignments: (i) the `⊆` proof now consumes `abelJacobiDiv`'s explicit-basepoint variant `abelJacobiDivAt X P₀` (per the refactor in `abelJacobiDiv.md`) so the Step 5 pole-avoidance basepoint feeds through cleanly; and (ii) this Forster residue + period-normalization route is now the **unified Abel-Jacobi infrastructure** consumed by `AX_ofCurve_inj` as well, replacing its previous Exponential Sheaf Sequence plan.

**Cross-plan patch (2026-06-03):** Standardised manifold-model-space notation to `𝓘(ℂ, ℂ)` (Mathlib's `modelWithCornersSelf ℂ ℂ`); the single-arg alias `𝓘(ℂ)` caused typeclass-unification failures between generic and concrete plans.
