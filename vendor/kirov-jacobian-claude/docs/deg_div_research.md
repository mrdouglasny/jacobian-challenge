# Research — cheapest Lean path to `deg_div` / `∑Res = 0` (the global residue / degree-of-a-principal-divisor wall)

Read-only recon for `/home/rado/jacobian`. Verified against the repo's Mathlib pin
(`8e3c989`, Lean `v4.30.0-rc1`) and Forster (GTM 81). Companion to
`docs/abel_riemannroch_research.md` and `docs/hodge_bridge_research.md`.

Legend: **[VERIFIED]** = confirmed by reading repo/Mathlib source, loogle/leansearch, or an
isolated `lake env lean` type-check this session; **[BOOK]** = Forster; **[BELIEVED]** = standard,
not re-derived.

---

## 0. Bottom line (recommendation)

**The wall is already decomposed in the repo, and the OLD "~400–900 LoC absent foundations" verdict
is now too pessimistic for the *book-keeping*, but essentially correct for the *irreducible analytic
atom*.** Three findings drive the recommendation:

1. **`deg_div` is NOT one monolithic sorry — it is two duplicate sorries plus a fully-proven
   reduction.** `Jacobians/DegDivResidue.lean` already proves `degDiv_eq_zero` (the residue theorem)
   from a *single* honest named sorry `exists_properMapDegree` (zeros-count = poles-count = a common
   proper-map degree `d`). All the `Finset`/order book-keeping (`deg = zerosCount − polesCount`) is
   done and axiom-clean. The *separate* `Jacobians/RiemannRoch.lean:290` `deg_div` sorry is logically
   **the same statement** and is dischargeable by `degDiv_eq_zero` (I type-checked
   `example … := degDiv_eq_zero f` — **it compiles** [VERIFIED]). So the true remaining content is
   `exists_properMapDegree`, not `deg_div`.

2. **The cheapest route is the repo's existing degree route — finish `exists_properMapDegree`.** It
   reuses the *already-axiom-clean* regular-fibre degree (`degreeFiber_eq_card_of_regularWitness`,
   `#print axioms` = `[propext, Classical.choice, Quot.sound]` [VERIFIED]) and the ℂℙ¹ manifold
   (`Jacobians/ProjectiveLine.lean`, `genus = 0`, two charts, `RiemannSphere`). What is genuinely
   missing is the **ramified-fibre count** (the degree counted at the special fibres over `0` and `∞`,
   where zeros/poles of order `> 1` sit) and its Rouché/argument-principle multiplicity bridge. Both
   are already *named and isolated* as inert `Prop`-defs (`argumentPrinciple_disk_statement`,
   `analytic_kth_root_branch_exists_statement`, `localMultiplicity_eq_localOrder_statement`), with the
   `k = 0` and `k = 1` cases **proven**.

3. **The new `resAt`/`residueSum`/`MittagLefflerForm` API does NOT shorten the global step.** It is a
   beautiful, sorry-free *local* residue calculus (additivity, ℂ-homogeneity, contour-independence,
   `Res(holo)=0`) — but it is exactly the *cochain-level* `Res`, and its own module docstring
   (`MittagLeffler.lean:35–47`) states the global, class-level `Res : H¹(X,Ω) → ℂ` is gated on the
   **same** `∑Res = 0 = deg_div`. So the residue API gives a *second consumer* of `deg_div`, not a
   cheaper *producer* of it. The Stokes/contour route it would support has no manifold-Stokes
   scaffolding in Mathlib (§3) and is strictly harder than the degree route the repo already chose.

**Revised LoC estimate for the irreducible atom: ~600–1200 LoC** (down from "400–900 absent
foundations", but the shape has changed: most of the *surrounding* machinery is now present/proven, so
the residual is more concentrated). The single hardest sub-atom is the **disk argument-principle
integral** `(2πi)⁻¹ ∮_{|z|=ε} g'/g = k` (`argumentPrinciple_disk_statement`), ~250–500 LoC, whose
Mathlib ingredients exist (`circleIntegral`, `MeromorphicAt.exists_eq_pow_smul`, Cauchy–Goursat on a
disk) but are not packaged. **It is still the hardest single classical wall on the forward
(genus-0/RR) endgame, and it is worth attempting *because* the repo already isolated it cleanly and
proved the easy slices.**

> **Caveat on "cheap" — the headline does NOT actually need general `deg_div`.** See §6: the headline
> `exists_singleSimplePole_of_genus_zero` consumes `deg_div` only through
> `lDim_eq_zero_of_deg_neg` for `deg D < 0`, and via the RR axiom. There is a real argument that the
> genus-0 endgame can be re-plumbed to avoid the *general* (ramified) residue theorem entirely,
> because the only `f` it ever builds has a **single simple pole** — exactly the case the repo's
> `degreeFiber_toSphere_eq_one` already handles with the regular-fibre degree alone. **If the goal is
> the headline, finishing the Serre/RR axiom is the gate, not `deg_div`** (§6.3). `deg_div` becomes
> mandatory only for the *general* RR equality and the *class-level* Serre `Res`.

---

## 1. The current `deg_div` statement (verbatim) and how it is consumed

### 1.1 The two duplicate statements

**(a) `Jacobians/RiemannRoch.lean:290`** (the named RR input):

```lean
/-- **The isolated residue-theorem input.** Every principal divisor has degree `0` (Forster
Cor. 4.25 / the argument principle). The RR derivations below consume it. -/
theorem MeromorphicFunction.deg_div (f : MeromorphicFunction X) :
    Divisor.deg X f.div = 0 := sorry
```
with `variable {X} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
[ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]`. (`Nonempty X` is free from `ConnectedSpace`.)

**(b) `Jacobians/DegDivResidue.lean:248`** (the degree-route theorem, **reduced to a smaller sorry**):

```lean
theorem degDiv_eq_zero (f : MeromorphicFunction X) :
    Divisor.deg X f.div = 0 := by
  obtain ⟨d, hz, hp⟩ := exists_properMapDegree f
  rw [deg_div_eq_zeros_sub_poles, hz, hp, sub_self]
```
(same hypotheses, plus an explicit `[Nonempty X]`). The book-keeping `deg_div_eq_zeros_sub_poles`,
`zerosCount`, `polesCount`, `deg_div_eq_support_sum` are **all proven, no analytic input.**

The genuine remaining sorry is **`exists_properMapDegree`** (`DegDivResidue.lean:213`):

```lean
theorem exists_properMapDegree (f : MeromorphicFunction X) :
    ∃ d : ℕ, zerosCount f = (d : ℤ) ∧ polesCount f = (d : ℤ) := sorry
```
with the trivial `f.div = 0` sub-case **proven** (`exists_properMapDegree_of_div_eq_zero`), confirming
the isolated statement is true, not vacuous.

> **[VERIFIED] The two are interchangeable.** I type-checked, against the live build:
> ```lean
> example {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
>     [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
>     (f : MeromorphicFunction X) : Divisor.deg X f.div = 0 := degDiv_eq_zero f
> ```
> — **compiles** (exit 0). So `RiemannRoch.deg_div`'s proof obligation is identically
> `exists_properMapDegree`. The repo currently carries *two* sorries for one fact only because of an
> import-layering accident (§1.3).

### 1.2 How `deg_div` is consumed

- **RR single-pole reduction (`RiemannRoch.lean`).** `deg_div` is used exactly once, in
  `lDim_eq_zero_of_deg_neg` (`RiemannRoch.lean:325`): for `deg D < 0`, any `f ∈ L(D)` with a nonzero
  germ would give `0 = deg(div f) ≥ −deg D > 0`. That `l(D) = 0` feeds `deg_canonical`,
  `lDim_canonical_eq_genus`, and the genus-0 endgame `exists_singleSimplePole_of_genus_zero_of_rr`.
  **It only ever uses `deg(div f) = 0` as an inequality witness `0 ≥ …`, never the ramified
  count directly.** [VERIFIED by reading the proof.]
- **Serre global residue (`Dolbeault/MittagLeffler.lean`).** The class-level
  `Res : cechH1 𝔘 Ω → ℂ` needs that a coboundary (a globally-meromorphic `α`) has total residue `0`,
  i.e. `∑_a Res_a(α) = 0` — the residue theorem, which the module docstring (`MittagLeffler.lean:41`)
  explicitly equates with `deg_div`. The *local* `residueSum` and its ℂ-linearity are built sorry-free;
  only the descent-through-the-quotient is gated. [VERIFIED.]

So `deg_div`/`∑Res=0` genuinely gates **both** consumers, as the brief states.

### 1.3 Architectural note (free win available, but layered)

`RiemannRoch.deg_div` and `DegDivResidue.degDiv_eq_zero` are the same obligation, but **`RiemannRoch`
cannot just write `:= degDiv_eq_zero`**: `DegDivResidue` imports `DegreeOneSphere`, which imports
`RiemannRoch` (`DegreeOneSphere.lean:10` — [VERIFIED] `grep import Jacobians.RiemannRoch`), so importing
`DegDivResidue` into `RiemannRoch` is a cycle. The clean fix (a separate, non-recon task) is to **lift
`exists_properMapDegree` + the `zerosCount/polesCount` book-keeping into a module upstream of
`RiemannRoch`** (it only needs `MeromorphicFunction.div`/`orderAtPoint` from `Abel`), then both
`RiemannRoch.deg_div` and `DegDivResidue.degDiv_eq_zero` reduce to it. That removes one of the two
duplicate sorries at zero math cost. **Recommend doing this regardless of which analytic route is
taken** — it makes "the residue wall" a single node.

---

## 2. Mathlib inventory verdict (present / absent)

### 2.1 PRESENT (verified this session)

| Capability | Mathlib name | Use to the residue wall |
|---|---|---|
| Circle integral + its algebra | `circleIntegral`, `circleIntegral.integral_add/_smul/_sub_inv_of_mem_ball`, `circleIntegral.integral_congr` | the contour engine the repo's `resAt` already builds on. [VERIFIED] |
| Cauchy–Goursat (disk / annulus, off countable) | `circleIntegral_eq_zero_of_differentiable_on_off_countable`, `circleIntegral_eq_of_differentiable_on_annulus_off_countable`, `…_sub_center_inv_smul_…_of_tendsto` (→ `2πi•y`) | radius-independence + single-residue; used in `Residue.lean`. **The single residue is here; the *counting* argument principle is not.** [VERIFIED] |
| Divergence theorem on **boxes** | `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable(_of_equiv)`, `integral_divergence_prod_Icc_of_hasFDerivAt…` | box/rectangle Green; powers the *flat* Stokes only. [VERIFIED] |
| Box / rectangle Cauchy | `Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable` (+ family) | flat Stokes-on-a-square; the repo's `CutSurface` uses it. [VERIFIED] |
| Meromorphic order, divisor (planar) | `meromorphicOrderAt`, `MeromorphicOn.divisor`, `divisor_apply`, `divisor_mul/_inv/_prod/_zpow`, `divisor_support_finite_of_subset`, `AnalyticOnNhd.divisor_nonneg` | the planar divisor algebra + finiteness on compact `U ⊆ ℂ`. [VERIFIED] |
| Order under products/powers | `meromorphicOrderAt` additivity (`Meromorphic/Order.lean:384` region), `MeromorphicOn.extract_zeros_poles` (build `f` from a planar divisor) | local normal form `f − w = (z−z₀)^k u`. [VERIFIED] |
| Local normal form (factor a zero) | `MeromorphicAt.exists_eq_pow_smul` / `analyticOrderAt_eq_natCast` / `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero` | the `(z−z₀)^k·u`, `u(z₀)≠0` factorization. [VERIFIED] — repo already uses these in `DegreeOneSphere.lean:457`. |
| **Jensen formula / Nevanlinna** | `MeromorphicOn.circleAverage_log_norm`, `AnalyticOnNhd.circleAverage_log_norm`, `AnalyticOnNhd.sum_divisor_le`, `countingFunction_finsum_eq_finsum_add`, `ValueDistribution.logCounting`, `locallyFinsuppWithin.logCounting_divisor` | **the integrated `circleAverage(log‖f‖)` counting** (`JensenFormula.lean`, `ValueDistribution/`). See §2.3 — relevant but NOT the `∮ f'/f` argument principle. [VERIFIED] |
| Liouville on compact manifolds | `MDifferentiable.exists_eq_const_of_compactSpace`, `apply_eq_of_compactSpace` | used in the repo's `MeromorphicLiouville`. [VERIFIED] |
| Proper map from ContMDiff | `IsProperMap` (repo `isProperMap_of_contMDiff`, `PeriodLattice.lean:1322`), `Continuous.isProperMap` | properness is *free* (compact source); the missing thing is **degree**, not properness. [VERIFIED] |
| ℂℙ¹ as a manifold | `Jacobians.RiemannSphere = OnePoint ℂ`, `ProjectiveLine.lean` (charts, `IsManifold`, `homeoSphere`, `genus = 0`) | the target of `f : X → ℂℙ¹`. **Built in-repo, axiom-clean.** [VERIFIED] |
| Regular-fibre degree | `Jacobians.degreeFiber`, `degreeFiber_eq_card_of_regularWitness` (**axiom-clean** [VERIFIED]), `RegularValueWitnessReg` | counts the fibre over a *regular* value; well-defined. **This is the asset.** |

### 2.2 ABSENT (would need building / is isolated in-repo)

- **The argument principle / Rouché counting** `(2πi)⁻¹ ∮_{|z−z₀|=ε} g'/g = #zeros−#poles`. *No*
  `windingNumber`, *no* `argumentPrinciple`, *no* `rouche` anywhere in Mathlib [VERIFIED, grep empty].
  Isolated in-repo as `argumentPrinciple_disk_statement` (`LocalNormalForm.lean:543`), with the
  `k = 0` case **proven** (`argumentPrinciple_disk_zero_case`).
- **Analytic `k`-th root branch** of a non-vanishing analytic function on a disk (the only block on the
  `k ≥ 2` Rouché count). Mathlib has `cpow`/`AnalyticOnNhd.cpow` but only on the *slit plane*
  (needs `f z ∈ slitPlane`), not a local branch around an arbitrary nonvanishing germ. Isolated as
  `analytic_kth_root_branch_exists_statement` (`LocalKFoldMultiplicity.lean:68`); `k = 1` **proven.**
  [VERIFIED]
- **Ramified fibre-count = degree.** `degreeFiber` counts only *regular* fibres; the extension to the
  special fibres over `0`/`∞` (zeros/poles, generally ramified) counted with multiplicity = the common
  degree is absent and is precisely the gap inside `exists_properMapDegree`. [VERIFIED]
- **Manifold Stokes / integration of differential forms on a manifold.** *Completely absent.* The only
  `Geometry/Manifold` hits for "Stokes" are `IntegralCurve` (ODE flows) and `Riemannian/PathELength`
  (arc length) — neither integrates a form; there is no `∫_X ω`, no de Rham, no manifold Stokes.
  [VERIFIED — grep over `Mathlib/` returns nothing relevant]. **This kills the manifold-Stokes route
  (§5.1) as a from-scratch effort.**
- **Topological / Brouwer mapping degree** of a continuous map (any `mapDegree`). Absent for this
  setting. (The repo's `degreeFiber` is a bespoke holomorphic fibre-cardinality degree, not a homology
  degree.) [VERIFIED]
- **A global "sum over a compact-surface divisor = 0".** Absent (`ValueDistribution` is planar/disk,
  about *integrated* counting functions, not a closed-surface identity). [VERIFIED]

### 2.3 The Jensen/Nevanlinna near-miss (important to be precise)

Mathlib's `JensenFormula.lean` + `ValueDistribution/` is the closest thing to "counting zeros and
poles", and it is genuinely substantial — but it computes
`circleAverage (log‖f·‖) c R = ∑ᶠ_u (divisor f) u · log(R/‖c−u‖) + log‖meromorphicTrailingCoeffAt f c‖`
(`MeromorphicOn.circleAverage_log_norm`, `JensenFormula.lean:120`). That is the **log-modulus** (real
potential-theoretic) form, *not* the **logarithmic-derivative winding** `∮ f'/f`. The two are siblings
(both follow from Cauchy), but:
- Jensen gives the *sum of orders weighted by `log`* against the boundary `log`-average. To extract the
  *unweighted* count `∑ord = winding` you still need the argument-principle integral, which Jensen does
  not provide.
- `AnalyticOnNhd.sum_divisor_le` gives an *inequality* (`∑ divisor ≤ log(M/‖f c‖)/log(R/r)`), i.e.
  Jensen's *inequality* (a Nevanlinna bound), not the *equality* `∑ord = winding number`.

**Verdict:** the Jensen machinery is reusable for the *finiteness*/*bound* facts (and is a strong
signal that Mathlib's complex-analysis foundations are maturing toward an argument principle), but it
does **not** discharge `argumentPrinciple_disk_statement`. The honest atom remains the `∮ f'/f`
identity. (Worth a watch: an upstream Mathlib argument-principle would collapse this wall — see §7.)

---

## 3. The routes compared

| # | Route | Foundation needed | ~LoC (residual) | Mathlib reuse | Risk |
|---|---|---|---|---|---|
| 1 | **Manifold-Stokes** `∑Res = ∫_X d(form) = 0` (Forster §17.3) | `∫` of a 2-form on a manifold **+** manifold Stokes (PoU + chart-square divergence) | **2000–4000+** | box-divergence only; **no** manifold form-integration | **Highest.** Building manifold form-integration + Stokes is a Mathlib-scale project; explicitly absent (§2.2). |
| 2 | **Degree route** (repo's chosen route): `deg(div f) = zeros − poles = d − d = 0`, both = proper-map degree | finish `exists_properMapDegree`: **(a)** disk argument principle `∮ g'/g = k`; **(b)** analytic `k`-th-root branch (`k≥2`); **(c)** ramified-fibre-count = `degreeFiber` | **600–1200** | **Large**: `degreeFiber` well-def (axiom-clean), ℂℙ¹ manifold, local normal form, `k=0`/`k=1` slices all present/proven | **Medium.** The atoms are isolated and the easy cases done; (a) is the hard concentrated piece but its ingredients exist. |
| 3 | **Map-degree (general)**: `deg(div f)` = degree of `f : X → ℙ¹` via fibre cardinality of a proper holomorphic map | a *homology* mapping-degree theory, OR exactly route 2's fibre-count | **(= route 2)** | none for a general topological degree; the repo's `degreeFiber` IS the holomorphic version | Same as route 2 (this *is* route 2 once you commit to fibre-cardinality rather than homology). |
| 4 | **Genus-0 / single-simple-pole shortcut** (sidestep general `deg_div`) | re-plumb the headline so it never needs the *general* (ramified) residue theorem — only the simple-pole degree, which `degreeFiber_toSphere_eq_one` already does with regular fibres | **200–500** (re-plumb) **+ 0** residue | the entire degree-1 endgame is **already proven** (`DegreeOneSphere.lean`) | **Medium, but real.** Needs the RR axiom re-derived without `lDim_eq_zero_of_deg_neg`'s general `deg_div` use — see §6.3. Removes `deg_div` from the headline critical path but **not** from Serre's class-level `Res`. |

### 3.1 Why route 1 (manifold Stokes) is the wrong target

Forster §17.3 proves `∑Res = 0` by writing the form as `d(η)` off the poles and integrating
`∫_X d(η) = 0` (Stokes on the surface minus small disks; the boundary circles give `−2πi ∑Res`). To
formalize this you need (i) integration of a 2-form over the compact manifold, and (ii) Stokes' theorem
on a manifold-with-boundary. **Mathlib has neither** (§2.2). Even the "cheat" of avoiding full
manifold-Stokes by triangulating into chart-squares and summing the box-divergence theorem requires a
triangulation / CW API and a "boundary edges cancel" combinatorial lemma — which is itself a large,
unscaffolded build (the repo's `CutSurface` is the closest, and it is one *specific* dissection, not a
general triangulation). **Estimate ≥ route 2 by a wide margin, with much weaker reuse.** Do not pursue.

### 3.2 Why route 2 is the recommendation

The repo *already committed* to route 2 and *already built almost all of it*:
- the order book-keeping (`deg = zerosCount − polesCount`) is **done**;
- the regular-fibre degree `degreeFiber` and its well-definedness are **done and axiom-clean**;
- ℂℙ¹ (the `ℙ¹` target) is **done** (`ProjectiveLine.lean`);
- the local normal form `f − w = (z−z₀)^k u` is reachable from Mathlib (`exists_eq_pow_smul`);
- the `k = 0` argument principle (`argumentPrinciple_disk_zero_case`) and the `k = 1` Rouché count
  (`localMultiplicityOne_preimage_card`) are **proven**.

What remains is concentrated in three named, isolated `Prop`-defs. This is the textbook "argument
principle" (Forster §4/Cor. 4.25, Miranda II.4), the standard proof, with standard Mathlib lemmas.

### 3.3 The per-chart cost is *low*; the global step is where it bites

The brief's route-2 question — "does the new `resAt`/`residueSum` make the per-chart step cheap,
leaving only a boundary-cancellation lemma?" — answer: **the per-chart *residue* is already cheap
(that is what `resAt`/`formFnResidue` give), but the degree route does not need boundary-cancellation
at all.** The degree route replaces "boundary contours cancel on a triangulation" (the Stokes idea)
with "both special fibres equal the *same* regular-fibre degree `d`" (a global topological-degree
constancy fact). The constancy is delivered by the *existing* `degreeFiber` well-definedness; the only
missing piece is connecting the *ramified* fibres over `0`/`∞` to that degree (the multiplicity
bridge). **So the residue API does not feed route 2** (route 2 is about *counts*, not contour
integrals), and it only feeds route 1 (which is dead). This is the crux of why the new API does not
lower the `deg_div` wall — it is upstream of the *Serre consumer* of `deg_div`, not a *producer*.

---

## 4. Recommendation + the precise first atom to build

**Route 2 (finish `exists_properMapDegree`), plus the free architectural unification of §1.3.**

The single highest-leverage, self-contained, sorry-free atom to build first — the irreducible analytic
heart — is the **disk argument-principle integral**, i.e. discharging
`argumentPrinciple_disk_statement`. Its Mathlib ingredients all exist; only the packaging is missing.
Concretely, a clean first target (one-variable complex analysis, no manifold, reusable in every chart):

```lean
/-- **Argument principle on a disk (the irreducible atom).**  For `g : ℂ → ℂ` analytic at `c` with
`analyticOrderAt g c = k`, the logarithmic-derivative contour integral counts the zero:
for all small `r > 0`,  `(2πi)⁻¹ ∮_{|z−c|=r} g'/g = k`.
Proof sketch: factor `g = (z−c)^k · u`, `u(c) ≠ 0` (`MeromorphicAt.exists_eq_pow_smul` /
`analyticOrderAt_eq_natCast`, already used at `DegreeOneSphere.lean:457`); then
`g'/g = k·(z−c)⁻¹ + u'/u`; the first term integrates to `2πi·k` (`resAt_const_mul_sub_inv`,
`circleIntegral.integral_sub_inv_of_mem_ball`), the second is holomorphic on a small disk
(`u(c) ≠ 0`) so integrates to `0` (`argumentPrinciple_disk_zero_case`, ALREADY PROVEN). -/
theorem argumentPrinciple_disk {g : ℂ → ℂ} {c : ℂ} {k : ℕ}
    (hg : AnalyticAt ℂ g c) (hk : analyticOrderAt g c = k) :
    ∃ ε₀ > (0 : ℝ), ∀ r ∈ Set.Ioo (0 : ℝ) ε₀,
      (2 * Real.pi * Complex.I)⁻¹ • (∮ z in C(c, r), deriv g z / g z) = (k : ℂ)
```

Why this is the right first atom:
- It is **pure ℂ-analysis, no manifold** — testable in isolation, reusable verbatim in every chart.
- It directly fills `argumentPrinciple_disk_statement`, which (via
  `argumentPrinciple_implies_rouche_statement`) yields the `k ≥ 2` Rouché count, completing the
  multiplicity bridge `localMultiplicity_eq_localOrder_statement`.
- Two of its three legs are **already proven** in the repo (`argumentPrinciple_disk_zero_case` for the
  holomorphic `u'/u` part; `resAt_const_mul_sub_inv` for the `k·(z−c)⁻¹` part). The genuinely new work
  is the **decomposition `g'/g = k/(z−c) + u'/u`** with `u` the nonvanishing factor (the log-derivative
  of a product), plus `CircleIntegrable` side-conditions. That is ~150–300 LoC.
- It is the *standard textbook* argument-principle proof — no bespoke machinery (matches the user's
  "prefer standard proofs" discipline).

After this atom, the residual `exists_properMapDegree` assembly is:
1. **`k ≥ 2` Rouché count** from the disk integral (the repo's `argumentPrinciple_implies_rouche`
   bridge + the `analytic_kth_root_branch_exists` packaging, OR — cheaper — derive the simple-zero
   count of `g − w` directly from the disk integral for small `w ≠ 0`, since each zero of `g − w` is
   simple, avoiding the `k`-th-root branch). ~300–500 LoC.
2. **ramified-fibre-count = `degreeFiber`**: the fibre over `0` (resp. `∞`), summed with the
   per-point multiplicities `= orderAtPoint`, equals the regular-fibre degree `d`. Reuse
   `degreeFiber_eq_card_of_regularWitness` + the existing critical-value-finite layer
   (`criticalValues_finite_general`). ~200–400 LoC.

**Did the new residue API lower the wall vs. the old ~400–900 LoC verdict?** *Marginally, and not where
it counts.* The `resAt`/`residueSum` calculus shaves the *single-residue* legs of the disk atom
(`resAt_const_mul_sub_inv`, `resAt_eq_zero_of_differentiableOn_ball`), worth maybe ~50–100 LoC, and is
exactly the right tool for the `k·(z−c)⁻¹` term. But it does **not** touch the two real costs (the
`g'/g` *decomposition* and the *ramified-count = degree* globalization), because those are not residue
computations. **Net: the wall is ~the same size as the old verdict (~600–1200), but it is now far
better *decomposed* — most of the surrounding scaffolding is present/proven, and the hard part is a
single, isolated, standard ℂ-analysis lemma rather than "absent foundations".** That is the genuine
improvement: the old "no scaffolding" is no longer true.

---

## 5. Detailed route notes (for whoever builds it)

### 5.1 Manifold-Stokes (route 1) — confirmed not worth it
Needs `∫_X` of a 2-form + Stokes. **[VERIFIED absent]**: grep over `Mathlib/Geometry/Manifold` for
Stokes/form-integration returns only `IntegralCurve` and `PathELength` (irrelevant). Building it is a
multi-thousand-LoC Mathlib-scale effort with no in-repo scaffolding. The box-divergence theorems
(`integral_divergence_…`, present) only give *flat* Stokes; assembling them into a surface integral
needs a triangulation API that does not exist (the repo's `CutSurface` is one specific dissection, not
reusable as a general triangulation). **Reject.**

### 5.2 Degree route (route 2) — the recommendation, fully mapped to existing code
- **Book-keeping** (`DegDivResidue.lean`): `deg = zerosCount − polesCount` — **done**.
- **Regular degree** (`Degree.lean`, `Discharge/Manifold/Degree.lean`, `DegreeWellDefined.lean`):
  `degreeFiber`, `degreeFiber_eq_card_of_regularWitness` — **done, axiom-clean** [VERIFIED].
- **ℂℙ¹ target + `toSphere`** (`ProjectiveLine.lean`, `DegreeOneSphere.lean`):
  `MeromorphicFunction.toSphere : X → RiemannSphere`, `contMDiff_toSphere`,
  `toSphere_preimage_infty`, `toSphere_regular_at_pole`, and the *simple-pole* degree
  `degreeFiber_toSphere_eq_one` — **done**. (This is the template for the ramified count: it shows
  exactly how a fibre's cardinality is read off as the degree at a regular value.)
- **Local normal form** (`LocalNormalForm.lean`, `LocalKFoldMultiplicity.lean`): `localOrder`,
  the `(z−z₀)^k·u` factorization, `localMultiplicity_one_locally_injective`,
  `kthRootSubstitution`, the `k=0`/`k=1` proven slices; `argumentPrinciple_disk_zero_case` **proven**.
- **The three remaining isolated gaps** (inert `Prop`-defs, not axioms):
  `argumentPrinciple_disk_statement` (§4 atom), `analytic_kth_root_branch_exists_statement`,
  `localMultiplicity_eq_localOrder_statement` (the manifold-level Rouché count) — **and** the
  ramified-fibre-count assembly inside `exists_properMapDegree`.

### 5.3 The `k`-th-root sidestep (saves the hardest secondary atom)
The `analytic_kth_root_branch_exists_statement` (needed to pass `card = 1` for `v` to `card = k` for
`g`) can be **avoided**: apply the disk argument principle to `g − w` for small `w ≠ 0`. Off the
order-`k` zero of `g`, `(g−w)'(z) = g'(z) ≠ 0`, so every zero of `g − w` near `c` is *simple*; the
disk integral then equals the *number* of such zeros directly (count = winding, each multiplicity 1),
and the open-mapping theorem gives there are exactly `k` of them. This routes the `k ≥ 2` count through
the disk integral + open mapping (both present) instead of an analytic `k`-th-root branch (absent).
**Recommend this path** — it removes one absent-from-Mathlib dependency.

---

## 6. Is this still the hardest wall — and should it be attempted before the others?

### 6.1 Ranking among the remaining walls
The repo's named open analytic inputs are: **(W1)** Serre/RR (`exists_riemannRoch_divisor`),
**(W2)** this residue theorem (`exists_properMapDegree`/`deg_div`), **(W3)** period-lattice full-rank
(`exists_cutSurface`, #7), **(W4)** Abel two-point (`abelJacobi_twoPoint_ne_zero`, #3),
**(W5)** the genus-comparison / `#6` off-branch leftovers.

- **W2 (residue) is NOT the hardest — W1 (Serre/RR) is.** W1 has no closed-form atom of comparable
  isolation; its kernel (the Dolbeault comparison + the finiteness node) is a much larger, multi-module
  build (see `docs/hodge_bridge_research.md`, `project_finiteness_node`). **W2 is the most
  *cleanly isolated* of the analytic walls**: a single standard ℂ-analysis lemma (the disk argument
  principle) plus a mechanical fibre-count assembly, all already named and with easy cases proven.
- **W2 vs. W3 (#7):** comparable scaffolding now (both have heavy box-Green/degree machinery), but W2's
  irreducible atom is *smaller and more standard* (argument principle vs. the period-matrix
  real-basis/Green build).

### 6.2 Should it be attempted before the others? — *Yes, with one caveat.*
**For effort-to-impact, W2 is the best single target to attack next**, because:
- it is the most isolated (one standard lemma + mechanical assembly);
- it unblocks **two** consumers at once (RR's `deg D < 0` vanishing *and* Serre's class-level `Res`);
- the free §1.3 unification removes a duplicate sorry immediately;
- almost everything around it is already proven, so success probability per LoC is high.

**Caveat (the honest part):** discharging W2 does **not by itself** close the headline — the headline
still needs W1 (the RR equality / Serre). So W2 is "highest-leverage *isolated* wall", but **W1 is the
gate**. If the single goal is the headline `genus_eq_zero_iff_homeo`, see §6.3.

### 6.3 The genus-0 shortcut (route 4) — real, and it *removes* `deg_div` from the headline
The headline forward direction (`exists_singleSimplePole_of_genus_zero`) uses `deg_div` only inside
`lDim_eq_zero_of_deg_neg` (to get `l(K−P) = 0`) and via the RR axiom. **But the only meromorphic
function the endgame ever *constructs* has a single simple pole**, and the repo *already* proves that
case's degree with regular fibres alone (`degreeFiber_toSphere_eq_one`, no Rouché, no ramified count).
So the *general* (ramified) residue theorem is **not** logically required for the headline — only:
- `l(K−P) = 0` for `deg(K−P) < 0`. This currently flows through general `deg_div`, but for a
  *single simple pole* `f` it can be obtained from the *simple-pole* degree fact directly (the only
  obstruction to `l(D)=0` is a function with `div f ≥ −D`, `deg(div f)=0`; for the divisors in play
  this reduces to the simple-pole case the repo already handles).
- The RR equality itself (W1) — *unavoidable*.

**Implication:** if the objective is the headline, **do not invest in the general ramified
`exists_properMapDegree` first** — invest in W1 (Serre/RR), and re-plumb `lDim_eq_zero_of_deg_neg` to
use the simple-pole degree (route 4, ~200–500 LoC re-plumb, *zero* new residue analysis). The
*general* `deg_div`/`∑Res=0` is mandatory only for **(i)** the general RR equality for arbitrary `D`
and **(ii)** Serre's class-level `Res : H¹(X,Ω)→ℂ`. Flag this clearly to the user: **"finish the
residue theorem" and "finish the headline" are different goals, and only the former truly needs
`exists_properMapDegree`.**

---

## 7. Upstream watch (could collapse the wall)
Mathlib's complex-analysis foundations are actively maturing toward the argument principle: the
`ValueDistribution` / `JensenFormula` modules (Nevanlinna theory, `circleAverage(log‖f‖)`,
`logCounting`) landed recently and are exactly the neighborhood an argument-principle / Rouché theorem
would live in. If an upstream `∮ f'/f = #zeros − #poles` (or a `windingNumber`/`mapDegree`) appears, the
§4 atom and most of `exists_properMapDegree`'s multiplicity bridge collapse to a citation. **Worth a
periodic `grep argumentPrinciple|windingNumber|rouche` on Mathlib bumps before investing the ~600–1200
LoC.** [BELIEVED — based on the trajectory of `Mathlib/Analysis/Complex/ValueDistribution`.]

---

## 8. Sources

**Primary (Forster, GTM 81):** §4 "The degree" + Cor. 4.24–4.25 (a meromorphic function has equally
many zeros and poles; `deg(f) = #f⁻¹(c)` independent of `c`); §16 Riemann–Roch (16.9); §17.1–17.3 the
residue of a meromorphic 1-form and the residue theorem `∑Res = 0` (the manifold-Stokes proof, route 1).
[BOOK] Miranda, *Algebraic Curves and Riemann Surfaces*, Ch. II §4 (degree / argument principle).
[BELIEVED]

**Repo (read this session):** `Jacobians/RiemannRoch.lean` (the `deg_div` sorry + single-pole
reduction), `Jacobians/DegDivResidue.lean` (the degree-route decomposition `degDiv_eq_zero` ⟸
`exists_properMapDegree`, all book-keeping proven), `Jacobians/Abel.lean` (`Divisor`, `deg`, `div`,
`orderAtPoint`), `Jacobians/Degree.lean` + `Discharge/Manifold/{Degree,DegreeWellDefined,
LocalNormalForm,LocalKFoldMultiplicity}.lean` (regular-fibre degree, axiom-clean; the isolated
argument-principle/Rouché `Prop`-defs with `k=0`/`k=1` proven), `Jacobians/ProjectiveLine.lean` (ℂℙ¹,
`genus=0`), `Jacobians/DegreeOneSphere.lean` (`toSphere`, the *simple-pole* degree-1 endgame — the
route-4 template), `Jacobians/Dolbeault/{Residue,FormCoeff,MittagLeffler,SerreDuality}.lean` (the new
sorry-free local residue calculus and its explicit gating on `deg_div`).

**Mathlib (verified by source/loogle/leansearch at pin `8e3c989`):**
`Analysis/Complex/CauchyIntegral.lean` (circle integral, Cauchy–Goursat, single residue → `2πi•y`;
**no argument principle**); `Analysis/Complex/JensenFormula.lean` +
`Analysis/Complex/ValueDistribution/{LogCounting,FirstMainTheorem,…}` (Jensen / Nevanlinna — integrated
`log`-counting, **not** `∮ f'/f`); `Analysis/Meromorphic/{Divisor,Order,FactorizedRational}.lean`
(planar divisor algebra, order under products/powers, `extract_zeros_poles`,
`exists_eq_pow_smul`/`analyticOrderAt_eq_natCast`); `MeasureTheory/Integral/DivergenceTheorem.lean` +
the `integral_boundary_rect_*` family (box/flat Stokes only); `Geometry/Manifold/Complex.lean`
(Liouville on compact manifolds). **No manifold Stokes, no manifold form-integration, no
windingNumber/argumentPrinciple/rouche, no general topological mapping degree, no compact-surface
divisor-degree identity.** [all VERIFIED]
