# Detailed formalization plan

**Target.** Close all 22 sorries in `Jacobians/Challenge.lean` (Buzzard's Jacobian Challenge v0.2), pinned to Mathlib commit `8e3c989104daaa052921bf43de9eef0e1ac9fbf5`.

**Chosen strategy.** Period-lattice construction in basis-free form, built on top of a standalone theta-function / abelian-variety library (Mumford Vol I Ch. II §§2–3). Everything Buzzard asks of the type `Jacobian X` — `AddCommGroup`, `TopologicalSpace`, `T2Space`, `CompactSpace`, `ChartedSpace (Fin (genus X) → ℂ)`, `IsManifold 𝓘(ℂ) ω`, `LieAddGroup` — is discharged from one general lemma: **any full-rank discrete subgroup of ℂ^g gives a quotient which is a compact complex Lie group**. The Riemann-surface-specific work is confined to producing the period matrix `τ(X) ∈ 𝔥_g`.

---

## 1. Consolidated source picture

What each reference contributes to the plan:

- **Mumford, *Tata Lectures on Theta I*, Ch. I §§1–4** (genus-1 warm-up): concrete `ϑ(z, τ)` definition, convergence, quasi-periodicity, projective embedding of `ℂ / (ℤ + ℤτ)`. Drives the ℝ² = ℂ case of every lemma in Part A before we attack general `g`.
- **Mumford Vol I, Ch. II §1**: several-variables theta `ϑ(z, Ω)` on `ℂ^g × 𝔥_g`. Convergence and quasi-periodicity generalize I §1 essentially line-by-line.
- **Mumford Vol I, Ch. II §2**: the Jacobian of a compact Riemann surface via period integrals of a normalized basis of holomorphic 1-forms. **Primary blueprint for Part B.**
- **Mumford Vol I, Ch. II §3**: `ϑ` and function theory on a compact Riemann surface — Abel-Jacobi, Abel's theorem (`ofCurve_inj`), Riemann's theorem on the theta divisor. Closes the payload theorems.
- **Mumford Vol I, Ch. II §4 + Appendix**: Siegel symplectic geometry — `Sp(2g, ℤ)`-action, generators, fundamental domain. Needed for dual / polarization; not on critical path for the 22 sorries.
- **Mumford Vol II, Ch. IIIa §5**: explicit hyperelliptic bridge between the analytic and algebraic Jacobians. Not needed to close the sorries, but the right optional cross-check (see §9 below).
- **Milne JV §§1–2**: functorial characterization of `J(C)` via `Pic⁰`; Abel-Jacobi as the "canonical map". Algebraic perspective; we don't formalize this definition but the theorems are the same, and it's the right sanity check.
- **Milne AV**: `Pic⁰`, dual abelian variety, Rosati involution, pairings. Structural vocabulary for `pushforward` / `pullback` functoriality.
- **Debarre §§1–2**: concise crystallization of the period-lattice construction and the Abel-Jacobi picture in ~3 pages. Useful as a cheat sheet.
- **Phase B survey (`docs/survey.md`)**: which pieces of Mathlib we can lean on vs. what we have to build.

---

## 2. Module architecture

```
Jacobians/
├── Challenge.lean               (verbatim from Buzzard, tracks upstream)
├── Basic.lean                   (shared imports, notation, conventions)
│
├── AbelianVariety/              ─── Part A: standalone abelian-variety machinery
│   ├── Lattice.lean             (FullRankLattice of ℂ^g, discreteness)
│   ├── Siegel.lean              (SiegelUpperHalfSpace g, topology, action)
│   ├── ComplexTorus.lean        (AbelianVariety τ, all 7 instances)
│   └── Theta.lean               (Riemann theta series, convergence, quasi-periodicity)
│
├── ProjectiveCurve/             ─── Track 2: concrete projective-curve models
│   ├── Charts.lean              (implicit-function-theorem utilities for zero loci)
│   ├── Line.lean                (ProjectiveLine = ℙ¹(ℂ), genus 0)
│   ├── Elliptic.lean            (curves in Weierstrass form; genus 1)
│   ├── Hyperelliptic.lean       (y² = f(x), explicit atlas, explicit 1-forms, explicit periods)
│   └── PlaneCurve.lean          (smooth homogeneous F ∈ ℂ[x,y,z]_d; Plücker genus)
│
├── RiemannSurface/              ─── Part B: Riemann-surface-specific constructions
│   ├── OneForm.lean             (HolomorphicOneForm X, ℂ-vector-space)
│   ├── PathIntegral.lean        (line integration of holo 1-forms along smooth paths)
│   ├── Homology.lean            (H_1(X, ℤ) via Mathlib π₁ + abelianization)
│   ├── Periods.lean             (period map, period matrix in 𝔥_g)
│   └── Genus.lean               (genus := dim_ℂ H⁰(X, Ω¹); genus = topological genus)
│
├── Jacobian/                    ─── bridge: plug Part B into Part A
│   ├── Construction.lean        (Jacobian X := AbelianVariety (τ X))
│   ├── AbelJacobi.lean          (ofCurve = period integral from P₀)
│   ├── Abel.lean                (ofCurve_inj — Abel's theorem)
│   ├── Functoriality.lean       (pushforward, pullback, ContMDiff.degree)
│   └── PushPull.lean            (pushforward_pullback = deg • id)
│
├── Genus0/                      ─── the one genuinely non-theta piece
│   └── Uniformization.lean      (genus_eq_zero_iff_homeo)
│
└── Axioms/                      ─── named deep facts, to be discharged later
    ├── FiniteDimOneForms.lean   (dim_ℂ H⁰(X, Ω¹) < ∞, with target dim = g)
    ├── Uniformization0.lean     (X genus 0 ⇒ X ≃ₜ S²)
    └── RiemannBilinear.lean     (Riemann's bilinear relations; τ is symmetric with Im τ > 0)
```

Design principles:
- Part A has **zero Riemann-surface dependence**. It's a reusable abelian-varieties-via-theta library, independently Mathlib-contributable.
- **Track 2** (`ProjectiveCurve/`) populates the space of concrete examples. Every type here satisfies Buzzard's typeclass constraints by construction (no appeal to Riemann existence). Track 2 depends on Part A (to use `AbelianVariety` for the Jacobian side), not on Part B.
- Part B depends on Mathlib (no differential forms on manifolds, per Phase B) plus `Axioms/`. Part B is what handles the *abstract* `X` side of Buzzard's challenge.
- `Jacobian/` is pure glue: take `τ(X)` from Part B, feed to Part A, get all instances for free.
- Track 2 closes Buzzard's sorries for every `X` that happens to be one of the explicit projective-curve types. It does not close them for an arbitrary abstract `X` — that's Part B's job.

---

## 3. Part A — Abelian varieties from theta

Purely linear-algebra and complex-analysis; no Riemann surfaces.

### 3.1 `AbelianVariety/Lattice.lean`

```
structure FullRankLattice (g : ℕ) where
  basis : Fin (2 * g) → ℂ × ... (Fin g → ℂ)  -- i.e., basis vectors in ℂ^g
  lin_indep_over_ℝ : LinearIndependent ℝ (fun i => ... Complex.realPart/imagPart ...)

def FullRankLattice.subgroup (Λ : FullRankLattice g) : AddSubgroup (Fin g → ℂ) := ...
```

Key lemmas:
- `FullRankLattice.discrete`: the subgroup is discrete in `Fin g → ℂ`.
  Proof: real linear independence gives `ℝ`-basis of `ℝ^(2g) ≃ Fin g → ℂ`, and integer lattice in any ℝ-basis is discrete.
- `FullRankLattice.isClosed`: closed subgroup of `Fin g → ℂ`.
- `FullRankLattice.quotient_isHausdorff`: follows from discreteness + `QuotientAddGroup.t2Space_of_discrete` (or build this if missing).

Difficulty: **Easy** (standard linear algebra + uses of Mathlib's existing `AddSubgroup` / `QuotientAddGroup` / `DiscreteTopology` APIs). **~2 days.**

### 3.2 `AbelianVariety/Siegel.lean`

```
def SiegelUpperHalfSpace (g : ℕ) : Type :=
  { τ : Matrix (Fin g) (Fin g) ℂ //
    τ.IsSymmetric ∧ (τ.map Complex.im).PosDef }
```

Key results:
- Open subset of `Matrix (Fin g) (Fin g) ℂ` → inherits complex-manifold structure (open subset of finite-dim ℂ-normed space).
- `SiegelUpperHalfSpace.lattice (τ) : FullRankLattice g` given by columns of `[I | τ]`.
- `Sp(2g, ℤ)`-action (optional for main challenge; needed for dual / polarization).

Difficulty: **Easy**. **~2 days.**

### 3.3 `AbelianVariety/ComplexTorus.lean`

The centerpiece of Part A. One definition, seven instances.

```
def AbelianVariety (Λ : FullRankLattice g) : Type := (Fin g → ℂ) ⧸ Λ.subgroup

namespace AbelianVariety
variable {g : ℕ} (Λ : FullRankLattice g)

instance : AddCommGroup (AbelianVariety Λ) := QuotientAddGroup.instAddCommGroup _
instance : TopologicalSpace (AbelianVariety Λ) := inferInstance  -- quotient topology
instance : T2Space (AbelianVariety Λ) := ...  -- from Λ.isClosed
instance : CompactSpace (AbelianVariety Λ) := ...  -- fundamental parallelogram + Λ full rank
instance : ChartedSpace (Fin g → ℂ) (AbelianVariety Λ) := ...  -- quotient map is a covering
instance : IsManifold 𝓘(ℂ, Fin g → ℂ) ω (AbelianVariety Λ) := ...  -- translations are holomorphic
instance : LieAddGroup 𝓘(ℂ, Fin g → ℂ) ω (AbelianVariety Λ) := ...  -- group ops smooth
```

Key sublemmas:
- `covering_map`: `π : (Fin g → ℂ) → AbelianVariety Λ` is a covering map.
- `local_section`: for each `p : AbelianVariety Λ`, a small neighborhood has a continuous section; on such neighborhoods `π` is a homeomorphism.
- `IsOpenEmbedding (restrict of π to a fundamental domain)`.

Difficulty: **Medium** — this is where the "quotient of a manifold by a discrete group action" gap shows up. Michael Rothgang's Mathlib in-flight work gives the ChartedSpace instance for general discrete group actions; we may need to inline parts of it or wait for upstream. Fallback: do the specific case of translation by `Λ` by hand (easier than the general case since `ℂ^g` is a group and the action is by translation). **~2–3 weeks** depending on upstream state.

### 3.4 `AbelianVariety/Theta.lean`

```
noncomputable def RiemannTheta (z : Fin g → ℂ) (τ : SiegelUpperHalfSpace g) : ℂ :=
  ∑' (n : Fin g → ℤ),
    Complex.exp (π * I * (bilinearForm τ.val n n) + 2 * π * I * (n • z))
```

Key lemmas (all standard in Mumford Vol I §I.1 for g=1, §II.1 for general g):
- `RiemannTheta.summable`: absolutely summable on compact sets (positive-definiteness of `Im τ` forces Gaussian-like decay of summands). Uses Mathlib's `Summable` + `tsum_comm` + Gaussian-decay estimates.
- `RiemannTheta.analytic_in_z`: holomorphic in `z` for fixed `τ`. Use Mathlib's `Analytic.sum` / `HasSum.analyticAt`.
- `RiemannTheta.quasi_periodic`: `ϑ(z + m + τ·n, τ) = exp(-π i n^T τ n - 2π i n^T z) · ϑ(z, τ)` for `m, n ∈ ℤ^g`.
- `RiemannTheta.heat_equation` (Vol I §I.2): the PDE satisfied by `ϑ`.

**Note.** Strictly, the 22 sorries in Challenge.lean don't require the theta series itself — the quotient `ℂ^g / Λ` already gives all 7 instances. Theta enters only if we want to prove the existence of sections of line bundles on the Jacobian (projective embedding), which is outside the challenge. So `Theta.lean` is optional from the perspective of the 22 sorries, but it is what unlocks the algebraic-geometric bridges and the broader Mumford programme, so we formalize it.

Difficulty: **Medium** (straightforward but detail-heavy series manipulations). **~2 weeks** for the core four lemmas above.

---

## 3.5 Track 2 — Concrete projective-curve constructions

Track 1 (Parts A + B) constructs `Jacobian X` for an arbitrary `X` satisfying Buzzard's typeclass constraints. **Track 2** runs in parallel: it populates the space of examples with explicit projective curves for which every instance is discharged by construction and every axiom in §7 is provable directly. Track 2 is not logically necessary for closing the 22 sorries on abstract `X`, but it gives us:

- a rich concrete population of `X`'s against which to test the abstract machinery,
- **proofs** (not axioms) of the §7 axioms for every `X` in that population,
- tractable, bounded targets for math-market / autonomous agents,
- a v0.1 showcase artifact independent of any deferred Riemann-existence bridge.

What Track 2 does *not* do: prove that every abstract `X` satisfying Buzzard's constraints is biholomorphic to one of these explicit models. That is Riemann's existence theorem / Chow's theorem, deferred as `AX_RiemannExistence` if/when formalized. Without that bridge, Track 2 closes Buzzard's sorries only for `X` that are of one of the explicit types below; Part B remains the path that closes them for arbitrary `X`.

### 3.5.1 `ProjectiveCurve/Line.lean`

```
def ProjectiveLine : Type := ℙ¹(ℂ)
```

Two standard charts `U₀ = {[z : 1]}` and `U₁ = {[1 : w]}`, transition `w = 1/z` on the overlap. Discharges all seven Buzzard instances explicitly.

Key facts:
- `HolomorphicOneForm ProjectiveLine` is the zero module (`ω_{ℙ¹} ≅ 𝒪(-2)` has no global sections). ⇒ `genus ProjectiveLine = 0`.
- `Jacobian ProjectiveLine` is a point (`g = 0` ⇒ lattice of rank 0 ⇒ ℂ^0 / 0 = pt).
- Explicit biholomorphism `ProjectiveLine ≃ Metric.sphere 1 ⊂ ℝ³` via stereographic projection. Closes the `⇐` direction of `genus_eq_zero_iff_homeo` concretely.

Difficulty: **Easy**. ~3 days.

### 3.5.2 `ProjectiveCurve/Elliptic.lean`

Built on Mathlib's `EllipticCurve` (Weierstrass form `y² = x³ + ax + b`). Charts: the affine open `z ≠ 0` in `ℙ²` plus a chart near the point at infinity via the standard change of variable.

Key facts:
- Genus 1.
- `HolomorphicOneForm` is 1-dim, spanned by `dx / y` on the affine chart (extended across infinity by the usual change-of-variable check).
- Period lattice `Λ ⊂ ℂ` via `ω_i = ∫_{γ_i} dx/y` for two generators `γ_1, γ_2` of `H_1(E, ℤ)`.
- Self-duality: `Jacobian E ≃ E` (as complex manifolds). Identifies the Abel-Jacobi map with the identity up to translation.

Difficulty: **Medium** — mostly reuses Mathlib's elliptic-curve infrastructure. ~2 weeks.

### 3.5.3 `ProjectiveCurve/Hyperelliptic.lean`

The workhorse. For `g ≥ 1` and squarefree `f : Polynomial ℂ` of degree `2g+1` or `2g+2`, define `HyperellipticCurve g f` as the smooth projective model of `y² = f(x)`.

Atlas: two affine patches glued along their common open. Patch A: `{(x, y) ∈ ℂ² : y² = f(x)}`. Patch B: `{(u, v) ∈ ℂ² : v² = u^{2g+2} · f(1/u)}` (or `u^{2g+1}·u·f(1/u)` in the odd-degree case, i.e., one branch point at infinity). Transition `(x, y) ↔ (1/u, v/u^{g+1})` on the overlap. Smoothness follows from squarefreeness of `f`.

Key facts:
- Genus = `g` (explicit basis of `HolomorphicOneForm`).
- **Explicit basis of `HolomorphicOneForm`:** `ω_k := x^k dx / y` for `k = 0, …, g-1`. The check of regularity at infinity uses the change of coordinates on the overlap.
- **Explicit period matrix:** with appropriate cycles `α_i, β_i` surrounding pairs of branch points, `τ[i, j] = (∫_{β_j} ω_i)/(∫_{α_j} ω_i)` after normalization. Each integral is a real one-variable improper integral of a rational function times `1/√f`, computable in Mathlib via `intervalIntegral` + residues.
- **Riemann bilinear relations** become residue calculus on the explicit model — this is `AX_RiemannBilinear` discharged, not axiomatized, in the hyperelliptic case.
- **`AX_FiniteDimOneForms` discharged** similarly: the `g` forms above span, and any holomorphic `ω` is written as `p(x, y) dx/y` with `p` polynomial bounded by adjunction; reduces to a polynomial-degree argument.
- **`AX_DegreeIndependence`** for maps between hyperelliptic curves follows from an explicit computation on coordinates.

This is where most of the Mumford Vol II §IIIa.1–5 material lives.

Difficulty: **Medium-hard** (real content, but concrete at every step). ~4 weeks.

### 3.5.4 `ProjectiveCurve/PlaneCurve.lean`

For homogeneous `F : HomogeneousPoly ℂ[x, y, z] d` with `d ≥ 3` and non-vanishing gradient on `{F = 0}`, define `SmoothPlaneCurve F := { [x:y:z] ∈ ℙ²(ℂ) : F(x, y, z) = 0 }`.

Three standard affine charts from `ℙ² = U_x ∪ U_y ∪ U_z`. On each `U_i`, the zero locus is an affine curve; by the implicit function theorem applied at any point where `∂F/∂x_j ≠ 0` for some `j ≠ i`, the curve is locally parametrized by the remaining coordinate. Holomorphicity of transitions is automatic from the algebraic defining data.

Key facts:
- **Genus by Plücker**: `g = (d-1)(d-2)/2`. Initially axiomatize (`AX_PluckerFormula`); prove later via adjunction.
- **Explicit `HolomorphicOneForm` basis by Poincaré residue**: for degree-`d` plane curves, a basis is `(polynomial in x, y of degree ≤ d-3) · (dx / ∂F/∂y)` restricted to the curve. Spanning is the adjunction formula.
- Covers many practically important cases: quartic plane curves (genus 3), quintics (genus 6), etc.

Difficulty: **Hard** (the implicit-function-theorem chart construction is fiddly; initial axiomatization of Plücker; explicit period-matrix computation nontrivial beyond hyperelliptic). ~6 weeks.

### 3.5.5 `ProjectiveCurve/Charts.lean`

Shared machinery:
- `implicitFunctionChart (f : analytic) (hrank : ...)` returns a `PartialHomeomorph` between a neighborhood in the zero locus of `f` and an open in `ℂ`.
- `PartialHomeomorph` constructors for zero-locus atlases on open subsets of `ℙ^n`.
- Proofs that compositions of projective and affine-chart changes restricted to the curve are holomorphic.

Most is wrappers around Mathlib's `Mathlib.Analysis.Calculus.ImplicitFunction` specialized to the 1-dim case. Difficulty: **Medium**. ~1–2 weeks.

### Track 2 payoff: which axioms become proofs

| Axiom | On abstract `X` | On `HyperellipticCurve g f` |
|-------|-----------------|-----------------------------|
| `AX_FiniteDimOneForms` | Hard (needs compactness + normal families) | **Proved** — explicit basis |
| `AX_RiemannBilinear` | Medium (integration by parts) | **Proved** — residue calculus on model |
| `AX_DegreeIndependence` | Medium | **Proved** — explicit coordinate computation |
| `AX_H1FreeRank2g` | Medium (CW topology) | **Proved** — standard `α_i, β_i` basis explicit |
| `AX_AbelTheorem` | Very hard (needs Riemann theta divisor) | **Likely provable directly** via residue calculus + principal-divisor argument, in hyperelliptic case |
| `AX_Uniformization0` | Hard (complex analysis) | **Proved** — `ProjectiveLine` is the explicit genus-0 case |

**Recommended ordering: Track 2 *before* finishing Part B.** After Part A (§§3.1–3.3) is done, do §3.5.1 (ProjectiveLine) and §3.5.3 (Hyperelliptic) *immediately*. On a hyperelliptic curve every Buzzard-side quantity — genus, 1-forms, period matrix, Abel-Jacobi map, pushforward/pullback under a covering `HyperellipticCurve g f → ProjectiveLine` — is computable in closed form. Use these computations as **sanity-check targets** when writing the abstract `HolomorphicOneForm` and `pathIntegral` in Part B: when the abstract machinery reproduces the concrete hyperelliptic answers, you've validated it.

---

## 4. Part B — Riemann-surface machinery

This is where Phase B (Mathlib-gap survey) bites hardest. None of `HolomorphicOneForm`, `PathIntegral`, or `H_1(X, ℤ)-for-manifolds` exists in the shape we need.

### 4.1 `RiemannSurface/OneForm.lean`

The type we need:

```
-- Auxiliary: pointwise, a holomorphic 1-form at p ∈ X is a ℂ-linear functional
-- on the complex tangent space T_p X (≃ ℂ).
-- Globally: a compatible assignment across charts.

structure HolomorphicOneForm (X : Type*)
    [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] where
  -- For each chart c : PartialHomeomorph X ℂ in the atlas, a holomorphic coefficient
  coeff : (c : PartialHomeomorph X ℂ) → c ∈ atlas ℂ X → (c.target → ℂ)
  holo  : ∀ c hc, AnalyticOn ℂ (coeff c hc) c.target
  cocycle : ∀ c₁ hc₁ c₂ hc₂, ∀ z ∈ c₁.target ∩ ..., 
    coeff c₂ hc₂ ((c₂ ∘ c₁.symm) z) * derivative (c₂ ∘ c₁.symm) z = coeff c₁ hc₁ z
```

Alternative (cleaner, but longer to set up): define `HolomorphicOneForm X` as ℂ-linear sections of the holomorphic cotangent bundle, with the bundle built by pushforward of `ℂ`-valued ℂ-linear functionals along charts. Phase B confirmed Mathlib has no cotangent-bundle API for complex manifolds; building it here would take weeks and be a Mathlib contribution in its own right. **Recommendation: go with the chart-cocycle definition**, which is concrete and enough for what we need.

Instances:
- `AddCommGroup (HolomorphicOneForm X)` — pointwise.
- `Module ℂ (HolomorphicOneForm X)` — pointwise.

Difficulty: **Medium-hard** (cocycle definition is fiddly but known territory). **~1–2 weeks.**

### 4.2 `RiemannSurface/PathIntegral.lean`

```
noncomputable def pathIntegral
    (γ : unitInterval →M X)  -- C^1 path
    (ω : HolomorphicOneForm X) : ℂ :=
  -- Partition γ into chart-sized pieces; on each piece γ lies in some chart c;
  -- set local contribution := ∫_{t ∈ segment} coeff c hc (c (γ t)) * derivative (c ∘ γ) t dt
  -- sum; chart-independence by the cocycle + chain rule.
  sorry
```

Key lemmas:
- `pathIntegral.well_defined`: independent of chart-partition choice (uses cocycle).
- `pathIntegral.additive`: `pathIntegral (γ₁ * γ₂) = pathIntegral γ₁ + pathIntegral γ₂` for concatenation.
- `pathIntegral.linear_in_form`: ℂ-linear in `ω`.
- `pathIntegral.reverse`: reversing γ negates the integral.
- `pathIntegral.homotopy_invariance`: for homotopic `γ₁ ~ γ₂` rel endpoints, `pathIntegral γ₁ ω = pathIntegral γ₂ ω`.

The homotopy-invariance is the analytic heart of the construction; it is the statement "d(∫ ω) = 0 because dω = 0", i.e., Stokes' theorem on a 2-disk for a closed 1-form. Math Inc. did this for paths in `ℂ` during the Viazovska autoformalization — confirm whether their lemmas are upstreamable or available.

Difficulty: **Hard** (real analytic content, needs care with chart partitions; homotopy invariance in particular is a nontrivial Stokes argument). **~3–4 weeks** if we can port Math Inc.'s ℂ-case; **~6–8 weeks** from scratch.

### 4.3 `RiemannSurface/Homology.lean`

First homology of `X` with ℤ coefficients. Mathlib has `FundamentalGroup X x₀` = `π₁(X, x₀)` (see `Mathlib/AlgebraicTopology/FundamentalGroupoid/FundamentalGroup.lean`). Define:

```
def H1 (X : Type*) [TopologicalSpace X] [PathConnectedSpace X] (x₀ : X) : Type :=
  Abelianization (FundamentalGroup X x₀)
```

Then via the universal property of abelianization, the period map `H₁(X, ℤ) → ℂ` factors through the fundamental group → (homotopy invariance of `pathIntegral`) → ℂ.

We additionally need: `H₁(X, ℤ)` is a free abelian group of rank `2g` when `X` is a compact oriented surface of genus `g`. This is classical topology (CW-structure, simplicial homology). **Do NOT attempt to formalize this from scratch** — axiomatize it in `Axioms/`, discharge later. For our purposes we only need the free-ℤ-module structure on `H₁`, which is provable from the presentation of compact oriented surfaces (standard generators `α_i, β_i` with one relation `∏ [α_i, β_i] = 1`, which abelianizes to nothing).

Difficulty: **Medium** for the definition; **axiomatize** rank = 2g. **~1 week.**

### 4.4 `RiemannSurface/Periods.lean`

The period map.

```
-- Period pairing
noncomputable def periodPairing (X : Type*) [...] :
    H1 X x₀ →+ (HolomorphicOneForm X →ₗ[ℂ] ℂ) :=
  -- Abelianization.lift of pathIntegral (seen as a group hom π₁ → additive group (HolomorphicOneForm X →ₗ[ℂ] ℂ))
  sorry

-- Period matrix (basis-dependent variant, for interface with Buzzard)
noncomputable def periodMatrix (X : Type*) [...]
    (α_basis : Basis (Fin (2*g)) ℤ (H1 X x₀))          -- symplectic basis axiomatized
    (ω_basis : Basis (Fin g) ℂ (HolomorphicOneForm X))
    : Matrix (Fin (2*g)) (Fin g) ℂ :=
  Matrix.of (fun i j => periodPairing (α_basis i) (ω_basis j))
```

Then normalize: solve linear system to get `[I | τ]` form, with `τ` the *normalized* period matrix in `𝔥_g`. Riemann's bilinear relations (Mumford Vol I §II.2, Thm II.2.1 and surroundings) give:
- `τ` is symmetric.
- `Im τ` is positive definite.

⇒ `τ ∈ SiegelUpperHalfSpace g`. **Axiomatize Riemann's bilinear relations** in `Axioms/RiemannBilinear.lean` initially; the proof is real-analytic (non-trivial integration by parts + positivity from Hodge star), doable but lengthy.

Difficulty: **Medium** (definition). Axiomatize the bilinear relations. **~1–2 weeks.**

### 4.5 `RiemannSurface/Genus.lean`

Two candidate genus definitions — need to prove equivalent:

- **Analytic genus**: `genusAnalytic X := Module.rank ℂ (HolomorphicOneForm X)` (cast to ℕ via `Module.rank.toNat`, once finite-dim is known).
- **Topological genus**: `genusTopological X := rank (H1 X x₀) / 2` (requires `H₁(X, ℤ)` free of even rank).

For closing Buzzard's `genus X : ℕ`: define `genus X := genusAnalytic X`. This makes `dim_ℂ (HolomorphicOneForm X) = genus X` a definitional equation, so the `ChartedSpace (Fin (genus X) → ℂ)` match is tautological once we choose a basis of `HolomorphicOneForm X`.

We need **Axiom (FiniteDimOneForms)**: `FiniteDimensional ℂ (HolomorphicOneForm X)`. Axiomatize.

Equivalence `genusAnalytic = genusTopological` is Hodge theory (the "`2g = b₁`" identity, equivalently `dim H¹_dR = 2 · dim H⁰(Ω¹)` for compact Kähler manifolds specialized to complex curves). Prove later; not needed for the 22 sorries.

Difficulty: **Easy** (definition only, deep facts axiomatized). **~3 days.**

---

## 5. Jacobian: bridging Part A and Part B

### 5.1 `Jacobian/Construction.lean`

```
-- τ-of-X: normalized period matrix
noncomputable def tau (X : Type*) [...] (basis data, axiomatized) : SiegelUpperHalfSpace (genus X) :=
  -- use periodMatrix + normalization
  sorry

noncomputable def Jacobian (X : Type*) [...] : Type :=
  AbelianVariety (SiegelUpperHalfSpace.lattice (tau X))
```

**All 7 instances Buzzard demands** (AddCommGroup, TopologicalSpace, T2Space, CompactSpace, ChartedSpace, IsManifold, LieAddGroup) **discharge automatically** from the corresponding instances on `AbelianVariety` in Part A. That's the payoff of the factorization: zero new Lean proofs for the instance soup.

Difficulty: **Easy** once Parts A and B are in place. **~2 days.**

### 5.2 `Jacobian/AbelJacobi.lean`

```
noncomputable def ofCurve {X : Type*} [...] (P₀ : X) : X → Jacobian X :=
  fun P =>
    -- pick a path γ : [0,1] → X from P₀ to P (needs PathConnectedSpace X)
    -- return [λ ω. pathIntegral γ ω] in (H^0)^∨ / Λ
    sorry
```

Well-definedness:
- `PathConnectedSpace X` comes from `ConnectedSpace X` + `LocallyPathConnectedSpace X`; locally path-connected follows from the chart structure. Add `LocallyPathConnectedSpace` as an immediate consequence of `ChartedSpace ℂ X`.
- Independence of path choice: any two paths `γ₁, γ₂` from `P₀` to `P` differ by a loop `γ₁ * γ₂⁻¹`, whose period integral lies in `Λ`. Modulo `Λ`, the answer is path-independent.

`ofCurve_self`: `ofCurve P₀ P₀ = 0` — integrate along the constant path.

Lemma `ofCurve_contMDiff`: the Abel-Jacobi map is holomorphic. Local expression: in a chart near `P`, `ofCurve P` is `z ↦ (∫_{z₀}^z ω_1, ..., ∫_{z₀}^z ω_g)` in terms of local chart coordinates and the chosen basis of `HolomorphicOneForm`. Each coordinate is holomorphic in `z` because the integrand is holomorphic. Use fundamental theorem of calculus (locally) + chart-compatibility.

Difficulty: **Medium-hard** (well-definedness + holomorphicity). **~2 weeks.**

### 5.3 `Jacobian/Abel.lean`

`ofCurve_inj`: `0 < genus X ⇒ Injective (ofCurve P₀)`. This is **Abel's theorem**, roughly: `∫_{P₀}^{P} ω = ∫_{P₀}^{Q} ω (mod Λ) for all ω ⇒ P = Q`.

Mumford Vol I §II.3.3–II.3.5 gives the classical proof. The argument:
1. Suppose `ofCurve P = ofCurve Q` with `P ≠ Q` and `g ≥ 1`.
2. Construct a meromorphic function on `X` with divisor `P - Q` — via Riemann's theorem on the theta divisor applied to `ofCurve`.
3. This contradicts the nonzero genus (constant meromorphic functions only).

**Recommendation**: this is the single hardest payload theorem. Consider **axiomatizing it initially** (`axiom abel_theorem : ∀ X [..] P₀, 0 < genus X → Function.Injective (ofCurve P₀)`) to unblock downstream work, and prove later via Riemann's theorem on theta.

Difficulty: **Very hard** if proved directly (requires Riemann's theorem on the theta divisor). **Axiomatize first**, dischage over months. **~8–12 weeks** end-to-end.

### 5.4 `Jacobian/Functoriality.lean`

For a holomorphic `f : X → Y` between compact Riemann surfaces:
- `f^* : HolomorphicOneForm Y → HolomorphicOneForm X` by precomposition: `(f^* ω).coeff c := ω.coeff (chart of Y on image of c's domain) ∘ f`, checking cocycle.
- `pushforward : Jacobian X → Jacobian Y` induced by integration of `f^* ω`.
- `pullback : Jacobian Y → Jacobian X` induced by integration along `f_*(γ)` for `γ ∈ H_1(X, ℤ)`.

Wait — the natural direction is:
- `f^* ω` (pulling back 1-forms) induces a map on `H⁰(X, Ω¹)^∨ → H⁰(Y, Ω¹)^∨` by **transpose**, which after quotienting by lattices gives `Jacobian X → Jacobian Y` — this is what Buzzard calls `pushforward`.
- `f_* γ` (pushing forward cycles) induces a map on `H_1(X, ℤ) → H_1(Y, ℤ)`, which in composition with period pairing gives `Jacobian X → Jacobian Y` — this matches.

So actually `pushforward` and the pullback-on-forms-transposed both point `X → Y`; that's consistent with naming.

For `pullback : Jacobian Y → Jacobian X`: the relevant input is `f^*` on H¹(Y, ℤ) → H¹(X, ℤ), dually `H_1(X, ℤ) → H_1(Y, ℤ)` ... no wait. Let me think again using Buzzard's actual signatures in the Challenge file: `pullback` goes `Jacobian Y → Jacobian X`, so it's induced by `f_*` on `H⁰(Y, Ω¹)^∨` (dual of `f^*` on forms gives this direction), modulo lattices. Matches.

**Contractions for the formalization**: factor through `H⁰(Ω¹)^∨` and `H_1` explicitly.

`ContMDiff.degree`: for `f : X → Y` non-constant holomorphic,

```
def ContMDiff.degree (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) : ℕ :=
  if hconst : (range f).Subsingleton then 0  
  else
    -- pick any regular value q ∈ Y; return the cardinality of f⁻¹(q) counted with multiplicity
    -- equivalently, for any point q ∈ Y, the divisor (f⁻¹(q), mult.) has the same total = deg f
    sorry
```

The standard approach on a Riemann surface is the residue/divisor formulation: for a non-constant holomorphic `f`, `deg f = #(f⁻¹ q)` at a regular value `q`, well-defined independent of `q` since `div(f-q₁) - div(f-q₂)` is principal. Mathlib has `Mathlib.Analysis.Meromorphic.Order.order` for the local order at a point; globalizing requires:
- Discreteness + finiteness of `f⁻¹ q` for `q` generic: follows from properness of `f` (compact `X`) + `f` being an open map (non-constant holo on Riemann surfaces).
- Independence of regular value: via connectedness of `Y` + local constancy of the counting function.

Difficulty: **Hard** for the full construction of `degree`; **medium** for the specialized lemmas. **~3–4 weeks.**

### 5.5 `Jacobian/PushPull.lean`

```
theorem pushforward_pullback (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (P : Jacobian Y) :
    pushforward f hf (pullback f hf P) = ContMDiff.degree f hf • P :=
  sorry
```

Mathematically: `f_* f^* ω = deg(f) · ω` on forms (basic fact from integrating along fibers). This descends to Jacobians.

Proof strategy:
1. Reduce to a statement about 1-forms: `⟨f_* f^* ω, γ⟩ = deg(f) · ⟨ω, γ⟩` for all `γ ∈ H_1(X, ℤ)` and `ω ∈ H⁰(Y, Ω¹)`. This is the statement in Mumford style.
2. Rewrite the LHS as an integral over `f⁻¹(γ)` and use the fiber counting.

Difficulty: **Medium-hard** once the infrastructure is in place. **~2 weeks.**

---

## 6. Genus-0 corner

### 6.1 `Genus0/Uniformization.lean`

```
theorem genus_eq_zero_iff_homeo
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] :
    genus X = 0 ↔ Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
```

This is **not a theta-function fact**. The `⇐` direction: the 2-sphere has `H⁰(S², Ω¹) = 0`, so `genus S² = 0`. The `⇒` direction is uniformization for genus 0: any genus-0 compact Riemann surface is biholomorphic to `ℂP¹`, hence homeomorphic to `S²`.

Approach: **axiomatize uniformization for genus 0** (`Axioms/Uniformization0.lean`). The full uniformization theorem is a deep piece of complex analysis; for genus 0 specifically, it reduces to: every compact Riemann surface with no holomorphic 1-forms is `ℂP¹`. This is strictly easier than the general uniformization theorem but still nontrivial (needs e.g. the fact that `H⁰(𝒪) = ℂ` plus some Riemann-Roch).

The `⇐` direction is independently provable: on `S²` = `ℂP¹`, holomorphic 1-forms are global sections of `𝒪(-2)` which is zero, so `H⁰(S², Ω¹) = 0`.

Difficulty: **Medium** for `⇐`, **axiomatize** for `⇒`. **~2–3 weeks** for the direction we can do.

---

## 7. Axiomatization strategy

We tag certain deep facts as named axioms initially — this lets downstream development proceed while we stage the hard proofs.

| Axiom | Statement | Proved in | Difficulty |
|-------|-----------|-----------|------------|
| `AX_FiniteDimOneForms` | `FiniteDimensional ℂ (HolomorphicOneForm X)` for `X` compact Riemann surface | Needs compactness + normal families / Serre duality | Hard |
| `AX_DimOneFormsEqGenus` | `Module.finrank ℂ (HolomorphicOneForm X) = genus X` (if genus is defined topologically) | Hodge theory | Hard; avoidable by taking `genus := dim H⁰(Ω¹)` |
| `AX_RiemannBilinear` | Period matrix is symmetric with pos-def imaginary part | Analytic integration by parts + Hodge-star | Medium |
| `AX_H1FreeRank2g` | `H₁(X, ℤ)` is free abelian of rank `2 · genus X` | CW / simplicial topology | Medium |
| `AX_Uniformization0` | `genus X = 0 → Nonempty (X ≃_holo ℂP¹)` | Classical complex analysis | Hard |
| `AX_AbelTheorem` | `0 < genus X → Function.Injective (ofCurve P₀)` | Riemann theta divisor | Very hard |
| `AX_DegreeIndependence` | The "counting preimages of a regular value" definition of degree is independent of the regular value | Principal divisors on Riemann surfaces | Medium |

**Rule**: every axiom gets its own file in `Axioms/`, with a docstring stating the math, the reference (Mumford / Milne / Debarre), and why it's axiomatized rather than proved. Each is a promissory note; we commit to discharging them eventually.

---

## 8. Dependency graph (critical path to closing 22 sorries)

```
Track 1 (abstract X):

Lattice → Siegel → ComplexTorus ─────────┐
                                          ├─→ Construction ─→ AbelJacobi ─→ Abel* ──┐
OneForm → PathIntegral ─→ Homology ──┐   │                                          │
                                      ├──┤                                          │
Genus (via dim of OneForm) ───────────┤   │                                          ├─→ ofCurve_inj
                                      └→ Periods → τ(X) ←─┘                        │
                                                                                    │
                                                    Functoriality ──→ PushPull ────┤
                                                                                    │
Axioms/Uniformization0 ─→ Genus0 ──────────────────────────────────────────────────┘
                                                                                    
                                                                                    └→ all 22 sorries closed for abstract X


Track 2 (concrete X from projective embedding; depends on Part A only):

Lattice → Siegel → ComplexTorus ──────────────┐
                                                ├─→ 22 sorries closed for these concrete X:
ProjectiveCurve/Charts.lean ─┬─→ Line.lean ─────┤       ProjectiveLine, EllipticCurve-from-Weierstrass,
                             ├─→ Elliptic.lean ──┤      HyperellipticCurve g f, SmoothPlaneCurve F
                             ├─→ Hyperelliptic ──┤
                             └─→ PlaneCurve ─────┘   (AX_* discharged explicitly on these types)
```

Asterisks = axiomatizable without breaking downstream work.

**Track 1 minimum viable build**: Parts A.1–A.3 + B.1–B.5 + Jacobian/Construction.lean — closes the 7 instance sorries + `genus` on abstract `X`.

**Track 2 minimum viable build**: Parts A.1–A.3 + ProjectiveCurve/{Charts, Line, Hyperelliptic} — closes **all** 22 sorries concretely on those types, with axioms discharged. Shippable independent of Part B.

After that, sorries fall in rough order of increasing difficulty:
1. `genus_eq_zero_iff_homeo` (⇐ direction), `ofCurve_self`
2. Functoriality identity lemmas (`pushforward_id_apply`, `pushforward_comp_apply`, analogously for pullback)
3. `ofCurve_contMDiff`, `pushforward_contMDiff`, `pullback_contMDiff` (holomorphicity)
4. `pushforward_pullback`
5. `ofCurve_inj` (Abel)
6. `genus_eq_zero_iff_homeo` (⇒ direction) — needs uniformization

---

## 9. Phases and rough time budget

Assumes a mix of Claude Code + human steering; costs multiplied by ~2 for full AI-autonomous.

Track 1 and Track 2 run largely in parallel after Part A is done.

| Phase | Content | Est |
|-------|---------|-----|
| A0 | Scaffold already done | — |
| A1 | `Basic.lean`, notation, test build | 1 day |
| A2 | `Lattice.lean` + `Siegel.lean` | 1 week |
| A3 | `ComplexTorus.lean` — all 7 instances | 2–3 weeks |
| A4 | `Theta.lean` — convergence + quasi-periodicity (optional for sorries) | 2 weeks |
| **A milestone** | **Part A standalone build, PR-able as Mathlib contribution** | **~5 weeks** |
| T1 | `ProjectiveCurve/Charts.lean` + `Line.lean` | 1–2 weeks |
| T2 | `ProjectiveCurve/Elliptic.lean` (leverages Mathlib) | 2 weeks |
| T3 | `ProjectiveCurve/Hyperelliptic.lean` — explicit atlas, 1-forms, period matrix, AX-discharges | 4 weeks |
| T4 | `ProjectiveCurve/PlaneCurve.lean` — implicit-function atlas, Poincaré residue basis | 6 weeks |
| **T milestone** | **22 sorries closed concretely on ProjectiveLine, Elliptic, Hyperelliptic; AX_\* proved on these** | **~8–10 weeks, concurrent with B** |
| B1 | `OneForm.lean` | 1–2 weeks |
| B2 | `PathIntegral.lean` — this is the hard one | 3–6 weeks |
| B3 | `Homology.lean` | 1 week |
| B4 | `Periods.lean` (axiomatize bilinear relations) | 1–2 weeks |
| B5 | `Genus.lean` | 3 days |
| **B milestone** | **`Jacobian X` defined and 7 instances close automatically on abstract X** | **~9 weeks after A done** |
| C1 | `AbelJacobi.lean`, `Functoriality.lean` | 3–4 weeks |
| C2 | `PushPull.lean` | 2 weeks |
| C3 | `Genus0/Uniformization.lean` (⇐ direction) | 2 weeks |
| C4 | `Abel.lean` (axiomatize first) | 1 week to set up, months to discharge |
| **C milestone (Track 1 challenge v0.2 closed modulo axioms)** | **~7 weeks after B done** |

Total to "Track 1 closed modulo axioms": **~5 months**. Track 2 comes out in **~3 months** (A + T in parallel) and has fewer axioms (most are discharged directly on the explicit curves). To "zero axioms on abstract X": significantly longer (12+ months), dominated by Abel's theorem via theta divisor + uniformization for genus 0.

---

## 10. Optional cross-checks and follow-ups

These are not on the critical path but raise the confidence / impact of the project:

- **Hyperelliptic Jacobian bridge** (Mumford Vol II §IIIa.5): formalize the analytic ↔ algebraic equivalence in the hyperelliptic case. Good sanity check for the period-matrix construction.
- **Genus-1 full explicit construction**: specialize everything to g=1, where the Jacobian is an elliptic curve. Mathlib already has elliptic curves — prove `Jacobian X ≃ EllipticCurve ℂ` for genus-1 `X`, reduces many calculations to Weierstrass form.
- **Algebraic side**: port Milne JV §1 definition of `Pic⁰(C)` as an abelian variety representing a functor. Prove `Jacobian X (analytic) ≃ Pic⁰(X (algebraic))` for the algebraic-categorified Riemann surface. Bridges to GAGA territory; probably too large to tackle inside this project but a natural followup.
- **Graph-limit / discrete analyticity**: use `graphops-qft` infrastructure to construct a discrete Jacobian on a triangulation and prove mesh-refinement convergence. Independent publishable artifact; serves as witness generator for the continuum-side lemmas.

---

## 11. Risks and fallback positions

- **`HolomorphicOneForm` definition gets tangled.** Fallback: start with the ℂP¹ case (trivial: `H⁰(Ω¹) = 0`), then the elliptic-curve case (well-known: `H⁰(Ω¹) ≃ ℂ`, spanned by `dz`), and only then attempt the general case. Both special cases fit inside Mathlib's existing machinery without cotangent bundles.
- **`PathIntegral` homotopy invariance drags.** Fallback: first prove `PathIntegral (closed loop bounding a disk in a single chart) = 0` (Cauchy on ℂ), then patch together chart-local disks via Stokes on a CW structure. Axiomatize the patch-argument if it resists.
- **Mumford `Sp(2g, ℤ)` action is surprisingly heavy.** We don't need this for the 22 sorries — skip for the main line.
- **Upstream Mathlib lands quotient-manifold-by-discrete-group before we do**: good for us. Re-align `ComplexTorus.lean` to use the upstream API.
- **Fails to build at all** on pinned Mathlib commit: fallback to a fresh Mathlib pin after `lake update`; Buzzard's file may need minor notation tweaks that he's happy to incorporate.

---

## 12. What we ship at v0.1

First milestone, aimed at publication / community signal. Shipped as **Track 2 + Part A + stubs for Track 1**:

1. Parts A.1–A.4 — complete standalone `AbelianVarieties` library (no sorries except optional `Theta.lean` lemmas).
2. `ProjectiveCurve/Line.lean`, `Elliptic.lean`, `Hyperelliptic.lean` — concrete projective curves satisfying all of Buzzard's typeclass constraints.
3. **All 22 sorries closed on `ProjectiveLine`, on genus-1 `EllipticCurve` examples, and on `HyperellipticCurve g f` for every squarefree `f`.**
4. Explicit period-matrix computations on those curves, with `AX_RiemannBilinear`, `AX_FiniteDimOneForms`, `AX_DegreeIndependence` **proved**, not axiomatized, on these models.
5. Definitions in Part B (`HolomorphicOneForm`, `pathIntegral`, `H_1`, `Jacobian X`) with signatures in place and explicit stubs; `Axioms/` directory populated with the seven named axioms.
6. Worked example: explicit `pushforward_pullback` identity verified on a genus-2 hyperelliptic curve mapping to `ℙ¹`.
7. CI green.

This is a substantive, defensible artifact to announce back on `#Autoformalization` with honest caveats: the 22 sorries are closed on *a rich concrete population of compact Riemann surfaces*, not on every abstract `X`; closing the abstract case is Part B + discharging the named axioms on abstract `X`, which is work in progress. Track 2 is what most practitioners will actually want to use.

## v0.2 target

1. Part B complete — `Jacobian X` for abstract `X` works, 7 instance sorries closed on abstract `X`.
2. Axioms `AX_FiniteDimOneForms`, `AX_RiemannBilinear`, `AX_H1FreeRank2g` documented and their *statements* match Track 2 proofs exactly (a "these are the same theorem" cross-check).
3. Functoriality (`pushforward`, `pullback`, `pushforward_pullback`) closed on abstract `X` modulo `AX_DegreeIndependence`.
4. `genus_eq_zero_iff_homeo` (⇐ direction) closed; (⇒) depends on `AX_Uniformization0`.

## v0.3 target

1. `AX_AbelTheorem` discharged via Riemann theta divisor on abstract `X` (needs `Theta.lean` fully in place).
2. `AX_Uniformization0` discharged.
3. `AX_RiemannExistence` — the bridge from abstract `X` to a projective model — attempted as a separate effort; if successful, Track 2 results transfer to abstract `X` automatically.
