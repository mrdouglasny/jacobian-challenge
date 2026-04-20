# Detailed formalization plan

**Target.** Close all 24 sorries in `Jacobians/Challenge.lean` (Buzzard's Jacobian Challenge v0.2), pinned to Mathlib commit `8e3c989104daaa052921bf43de9eef0e1ac9fbf5`.

**Chosen strategy.** Period-lattice construction, **basis-free at the type level**. The Jacobian is defined as `(HolomorphicOneForm X →ₗ[ℂ] ℂ) ⧸ periodImage(X)` — a quotient of the dual of holomorphic 1-forms by the image of `H_1(X, ℤ)` under integration. The Siegel period matrix `τ(X) ∈ 𝔥_g` is a *theorem* about this Jacobian (after choosing a basis), not its definitional foundation. Everything Buzzard asks of `Jacobian X` (`AddCommGroup`, `TopologicalSpace`, `T2Space`, `CompactSpace`, `ChartedSpace (Fin (genus X) → ℂ)`, `IsManifold 𝓘(ℂ) ω`, `LieAddGroup`) reduces to one general lemma: *any full-rank discrete additive subgroup of a finite-dimensional ℂ-vector space gives a compact complex Lie group as its quotient*.

> **Amendment log (2026-04-20, round 1).** Reviewed by Gemini 3 Pro; see [`gemini-review.md`](gemini-review.md) for the full review + triage. Key amendments: (1) Jacobian redefined basis-free above; (2) `HolomorphicOneForm` Mathlib cotangent-bundle check precedes chart-cocycle commitment; (3) new `RiemannSurface/IntersectionForm.lean` module for intersection pairing + Hurewicz + period injectivity; (4) `AX_Uniformization0` replaced by `AX_RiemannRoch`; (5) time budget revised upward; (6) `IsZLattice` preferred; (7) `Complex.cpow` branch cuts flagged as first-class risk; (8) Lie-group instance proposed via `AddCircle` transport.
>
> **Amendment log (2026-04-20, round 2).** Subsequently reviewed by GPT-5 via Codex; see [`codex-review.md`](codex-review.md). Codex checked the pinned Mathlib tree and found several concrete gaps Gemini missed. Round-2 amendments: (A) `AddCircle` transport retracted — `AddCircle`'s Lie group structure is still `TODO` at the pin, so we build the complex-Lie-group structure on `V/Λ` directly from local charts. (B) `τ`-based references in §2 and §8 swept out; basis-free `Jacobian X := JacobianAmbient X ⧸ periodLattice X` is the only architecture. (C) `genus` normalized to `Module.finrank ℂ (HolomorphicOneForm X)` everywhere; `FiniteDimensional ℂ (HolomorphicOneForm X)` required as a global *instance* before any `finrank` or `ChartedSpace` declaration. (D) Chart-cocycle fallback reformulated against Mathlib's `extendCoordChange` + `mfderiv` API. (E) `ContMDiff.degree` redefined via `meromorphicOrderAt` (order of `f - q` at local points), not via regular-value preimages (Sard is `TODO` at the pin). (F) `AX_SerreDuality` added as a named axiom (was implicit in the genus-0 proof). (G) Track 2 `HyperellipticCurve` commits to explicit lifted path parameterizations on slit domains; `Complex.cpow` is out of scope for the first implementation pass. (H) v0.1 ship target no longer promises a fully worked `pushforward_pullback` genus-2 example — only the definitional skeleton + axiomatized fiber theory.

---

## 1. Consolidated source picture

What each reference contributes to the plan:

- **Mumford, *Tata Lectures on Theta I*, Ch. I §§1–4** (genus-1 warm-up): concrete `ϑ(z, τ)` definition, convergence, quasi-periodicity, projective embedding of `ℂ / (ℤ + ℤτ)`. Drives the ℝ² = ℂ case of every lemma in Part A before we attack general `g`.
- **Mumford Vol I, Ch. II §1**: several-variables theta `ϑ(z, Ω)` on `ℂ^g × 𝔥_g`. Convergence and quasi-periodicity generalize I §1 essentially line-by-line.
- **Mumford Vol I, Ch. II §2**: the Jacobian of a compact Riemann surface via period integrals of a normalized basis of holomorphic 1-forms. **Primary blueprint for Part B.**
- **Mumford Vol I, Ch. II §3**: `ϑ` and function theory on a compact Riemann surface — Abel-Jacobi, Abel's theorem (`ofCurve_inj`), Riemann's theorem on the theta divisor. Closes the payload theorems.
- **Mumford Vol I, Ch. II §4 + Appendix**: Siegel symplectic geometry — `Sp(2g, ℤ)`-action, generators, fundamental domain. Needed for dual / polarization; not on critical path for the 24 sorries.
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
│   ├── OneForm.lean             (HolomorphicOneForm X; prefer Mathlib CotangentBundle if usable)
│   ├── PathIntegral.lean        (line integration of holo 1-forms along smooth paths)
│   ├── Homology.lean            (H_1(X, ℤ) via Mathlib π₁ + Abelianization + Hurewicz bridge)
│   ├── IntersectionForm.lean    (symplectic intersection on H_1; period-map injectivity)
│   ├── Periods.lean             (period map, period matrix in 𝔥_g, Riemann bilinear)
│   └── Genus.lean               (genus := dim_ℂ H⁰(X, Ω¹); genus = topological genus)
│
├── Jacobian/                    ─── bridge: plug Part B into Part A (basis-free)
│   ├── Construction.lean        (Jacobian X := JacobianAmbient X ⧸ periodLattice X)
│   ├── AbelJacobi.lean          (ofCurve = period integral from P₀)
│   ├── Abel.lean                (ofCurve_inj — Abel's theorem)
│   ├── Functoriality.lean       (pushforward, pullback, ContMDiff.degree via order)
│   └── PushPull.lean            (pushforward_pullback = deg • id)
│
├── Genus0/                      ─── the one genuinely non-theta piece
│   └── Uniformization.lean      (genus_eq_zero_iff_homeo)
│
└── Axioms/                      ─── named deep facts, to be discharged later
    ├── FiniteDimOneForms.lean   (FiniteDimensional ℂ (HolomorphicOneForm X); installed as instance)
    ├── RiemannBilinear.lean     (period matrix is symmetric with pos-def imaginary part)
    ├── RiemannRoch.lean         (Riemann–Roch; implies AX_Uniformization0 as a theorem)
    ├── SerreDuality.lean        (Serre duality for compact Riemann surfaces; needed in genus-0 proof)
    ├── PeriodInjective.lean     (H_1(X, ℤ) → (H⁰(X, Ω¹))^∨ is injective)
    ├── H1FreeRank2g.lean        (H_1(X, ℤ) free abelian of rank 2·genus)
    ├── AbelTheorem.lean         (0 < genus ⇒ ofCurve injective)
    ├── BranchLocus.lean         (branch locus of f : X→Y is finite; fiber cardinality = deg)
    └── PluckerFormula.lean      (smooth plane curve of degree d has genus (d-1)(d-2)/2)
```

Design principles:
- Part A has **zero Riemann-surface dependence**. It's a reusable abelian-varieties-via-theta library, independently Mathlib-contributable.
- **Track 2** (`ProjectiveCurve/`) populates the space of concrete examples. Every type here satisfies Buzzard's typeclass constraints by construction (no appeal to Riemann existence). Track 2 depends on Part A, not on Part B.
- Part B depends on Mathlib (no differential forms on manifolds, per Phase B) plus `Axioms/`. Part B is what handles the *abstract* `X` side of Buzzard's challenge.
- **`Jacobian/` bridges basis-free**: `Jacobian X := JacobianAmbient X ⧸ periodLattice X`, where `JacobianAmbient X := HolomorphicOneForm X →ₗ[ℂ] ℂ` and `periodLattice X := range periodMap`. No `τ`-matrix is baked into the *definition*; the Siegel period matrix is a derived theorem after choosing a basis. The seven Buzzard instances transfer from Part A's `AbelianVariety` applied to `V := JacobianAmbient X` and `Λ := periodLattice X`.
- Track 2 closes Buzzard's sorries for every `X` that happens to be one of the explicit projective-curve types. It does not close them for an arbitrary abstract `X` — that's Part B's job.

---

## 3. Part A — Abelian varieties from theta

Purely linear-algebra and complex-analysis; no Riemann surfaces.

### 3.1 `AbelianVariety/Lattice.lean`

**First: Mathlib survey.** Mathlib likely has `IsZLattice` / `ZLattice` in `Mathlib/Algebra/Module/ZLattice/Basic.lean` (or `Mathlib/Geometry/IsZLattice.lean`). If `IsZLattice ℝ V` exists at the pinned commit with the expected API (discreteness, fundamental domain, closed subgroup, quotient T2), **use it directly** rather than rolling our own. This gives us for free:
- Discreteness (`IsZLattice.discrete` or equivalent)
- Closed as an `AddSubgroup`
- Hausdorffness of the quotient via `DiscreteTopology → T2Space_of_quotient`

**Fallback** (if Mathlib API is missing or incompatible at pin):

```
structure FullRankLattice (V : Type*) [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] where
  basis : Fin (Module.finrank ℝ V) → V
  lin_indep_over_ℝ : LinearIndependent ℝ basis
```

Then `FullRankLattice.subgroup : AddSubgroup V` via ℤ-span. Key lemmas as before: discreteness, closedness, T2-of-quotient.

**Generalize away from `Fin g → ℂ`.** We want lattices in an *arbitrary* finite-dim ℂ-vector space (because the basis-free Jacobian lives in `(HolomorphicOneForm X →ₗ[ℂ] ℂ)`, not in `ℂ^g`). So the lattice type is parametrized by the ambient space, not by a numerical dimension.

Difficulty: **Easy** if `IsZLattice` is available; **~2 days**. **Medium** if we write from scratch (mostly tedious but straightforward); **~1 week**.

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
def AbelianVariety (V : Type*) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ChartedSpace V V]
    [IsManifold 𝓘(ℂ, V) ω V]
    (Λ : IsZLattice ℝ V)             -- or FullRankLattice V in the fallback
    : Type := V ⧸ Λ.subgroup

-- All seven instances for AbelianVariety V Λ, in order
```

Strategy for each instance:
1. `AddCommGroup`, `TopologicalSpace`: `QuotientAddGroup` and quotient topology — both automatic.
2. `T2Space`: immediate from Λ being a closed subgroup of a Hausdorff group (both `IsZLattice` and our fallback provide this).
3. `CompactSpace`: the quotient `V/Λ` is compact iff Λ has full real rank (⇒ image of fundamental parallelotope covers, which is compact in `V`). Standard.
4. `ChartedSpace V (AbelianVariety V Λ)`: the quotient map `π : V → V/Λ` is a covering map (by discreteness). For each `p ∈ V/Λ`, a sufficiently small neighborhood of any lift `v ∈ π⁻¹(p)` is homeomorphic to a neighborhood of `p` under `π`. Each such local section gives a `PartialHomeomorph`.
5. `IsManifold 𝓘(ℂ, V) ω`: transition maps between overlapping local sections differ by translation by a lattice vector, which is holomorphic. ⇒ transitions are `AnalyticOn ℂ`.
6. `LieAddGroup 𝓘(ℂ, V) ω`: **Direct construction from local charts.** Codex review flagged that `AddCircle`'s Lie group structure is still `TODO` in Mathlib at the pin (`Mathlib/Topology/Instances/AddCircle/Defs.lean:48-50`), so the "transport from `(AddCircle)^{2g}`" shortcut the plan previously proposed is not available yet. Instead, prove `LieAddGroup` directly: lift addition on `V/Λ` to addition on `V` via the covering map; addition on `V` is a polynomial (hence analytic) map `V × V → V`; it descends to `V/Λ × V/Λ → V/Λ` smoothly because translations by lattice vectors preserve the quotient and are themselves holomorphic. Negation is analogous. Use `ContMDiff.comp_contMDiff` and the covering-map structure from (4) to bundle.

**Upstream dependency note.** If Mathlib lands either:
- `AddCircle` Lie-group structure (the `TODO`), or
- A generic "complex manifold quotient by a discrete group" API (Rothgang's in-flight work),

then re-align `ComplexTorus.lean` to use the upstream API. But don't wait for either — the direct-from-local-charts proof above is straightforward given §3.3 items 4–5.

Difficulty: **Medium**; **~3–4 weeks** for the direct construction. The covering-map structure in step (4) is where most of the work lives; the Lie-group smoothness in (6) reduces mechanically once (4) and (5) are in place.

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

**Note.** Strictly, the 24 sorries in Challenge.lean don't require the theta series itself — the quotient `ℂ^g / Λ` already gives all 7 instances. Theta enters only if we want to prove the existence of sections of line bundles on the Jacobian (projective embedding), which is outside the challenge. So `Theta.lean` is optional from the perspective of the 24 sorries, but it is what unlocks the algebraic-geometric bridges and the broader Mumford programme, so we formalize it.

Difficulty: **Medium** (straightforward but detail-heavy series manipulations). **~2 weeks** for the core four lemmas above.

---

## 3.5 Track 2 — Concrete projective-curve constructions

Track 1 (Parts A + B) constructs `Jacobian X` for an arbitrary `X` satisfying Buzzard's typeclass constraints. **Track 2** runs in parallel: it populates the space of examples with explicit projective curves for which every instance is discharged by construction and every axiom in §7 is provable directly. Track 2 is not logically necessary for closing the 24 sorries on abstract `X`, but it gives us:

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
- **Explicit period matrix:** with appropriate cycles `α_i, β_i` surrounding pairs of branch points, `τ[i, j] = (∫_{β_j} ω_i)/(∫_{α_j} ω_i)` after normalization. **Cycles are parameterized explicitly as lifted paths in the two-sheet atlas**: each `α_i, β_i` is given as a concrete map `[0, 1] → HyperellipticCurve g f` that takes an arc in the upper or lower half plane (avoiding branch points) and lifts it to the correct sheet. The integral is then a real one-variable integral along the parameterization — no `Complex.cpow` branch cuts are invoked, and the sheet choice on `α` vs `β` is explicit in the parameterization. (This corrects the earlier plan draft which suggested `intervalIntegral` + residues could absorb the sheet choice; Codex review correctly flagged that this hides the branch-choice problem rather than solving it.)
- **Riemann bilinear relations** become residue calculus on the explicit model — this is `AX_RiemannBilinear` discharged, not axiomatized, in the hyperelliptic case.
- **`AX_FiniteDimOneForms` discharged** similarly: the `g` forms above span, and any holomorphic `ω` is written as `p(x, y) dx/y` with `p` polynomial bounded by adjunction; reduces to a polynomial-degree argument.
- **`AX_BranchLocus`** for maps between hyperelliptic curves follows from explicit coordinate computation: branch locus is where `f'(x) = 0`, i.e. a finite set of polynomial roots; fiber cardinality away from branches is exactly the degree of the covering polynomial.

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
| `AX_BranchLocus` | Medium | **Proved** — finite branch points are roots of `f'`, fiber cardinality 2 on regular values |
| `AX_H1FreeRank2g` | Medium (CW topology) | **Proved** — standard `α_i, β_i` basis explicit |
| `AX_AbelTheorem` | Very hard (needs Riemann theta divisor) | **Likely provable directly** via residue calculus + principal-divisor argument, in hyperelliptic case |
| `genus_eq_zero_iff_homeo` (⇐) | Medium — needs explicit biholomorphism `X ≃ ℙ¹` first | **Proved** — `ProjectiveLine` explicitly has `H⁰(Ω¹) = 0` and is homeo to `S²` via stereographic projection |

**Recommended ordering: Track 2 *before* finishing Part B.** After Part A (§§3.1–3.3) is done, do §3.5.1 (ProjectiveLine) and §3.5.3 (Hyperelliptic) *immediately*. On a hyperelliptic curve every Buzzard-side quantity — genus, 1-forms, period matrix, Abel-Jacobi map, pushforward/pullback under a covering `HyperellipticCurve g f → ProjectiveLine` — is computable in closed form. Use these computations as **sanity-check targets** when writing the abstract `HolomorphicOneForm` and `pathIntegral` in Part B: when the abstract machinery reproduces the concrete hyperelliptic answers, you've validated it.

---

## 4. Part B — Riemann-surface machinery

This is where Phase B (Mathlib-gap survey) bites hardest. None of `HolomorphicOneForm`, `PathIntegral`, or `H_1(X, ℤ)-for-manifolds` exists in the shape we need.

### 4.1 `RiemannSurface/OneForm.lean`

**First: Mathlib survey.** Gemini 3 Pro reasonably pushed back on chart-cocycle as an anti-pattern in Lean 4 / Mathlib. Before committing, check whether Mathlib at the pinned commit has a usable cotangent-bundle / vector-bundle API that applies to complex manifolds:
- `Mathlib/Geometry/Manifold/VectorBundle/Tangent.lean` (tangent bundle)
- `Mathlib/Geometry/Manifold/ContMDiff/Bundle.lean` (sections)
- `Mathlib/Geometry/Manifold/MFDeriv/` (manifold derivatives)

If a cotangent-bundle API is there and `ContMDiffSection 𝓘(ℂ) ω (cotangentBundle X)` is a reasonable expression, define:

```
def HolomorphicOneForm (X : Type*) [...] : Type :=
  { ω : SomeCotangentSection X // IsHolomorphic ω }
```

If not, fall back to the chart-cocycle approach. Codex review flagged that writing the cocycle with raw `c₂ ∘ c₁.symm` derivatives is not aligned with Mathlib's actual API. The idiomatic formulation uses `extendChartAt` (extended charts returning a `PartialEquiv` into the model vector space) and `fderivWithin` on the chart overlap `range I`:

```
structure HolomorphicOneFormCocycle (X : Type*) [...] where
  /-- local coefficient for each chart in the atlas -/
  coeff    : ∀ (x : X), (extChartAt 𝓘(ℂ) x).target → ℂ
  holo     : ∀ x, AnalyticOn ℂ (coeff x) (extChartAt 𝓘(ℂ) x).target
  /-- compatibility, phrased via extendCoordChange -/
  cocycle  : ∀ x y, ∀ z ∈ ((extChartAt 𝓘(ℂ) x).target ∩ (extChartAt 𝓘(ℂ) y).source.image ...),
               coeff y ((extendCoordChange 𝓘(ℂ) x y) z)
                 * fderivWithin ℂ (extendCoordChange 𝓘(ℂ) x y) (range 𝓘(ℂ)) z 1
               = coeff x z
```

Key Mathlib API to use:
- `extChartAt 𝓘(ℂ) x : PartialEquiv X ℂ` (`Mathlib/Geometry/Manifold/IsManifold/ExtChartAt.lean`).
- `contDiffWithinAt_extendCoordChange` (holomorphicity of chart transitions).
- `isInvertible_fderivWithin_extendCoordChange` (the transition derivatives are invertible).
- `mfderiv = fderiv` on model spaces (`Mathlib/Geometry/Manifold/MFDeriv/FDeriv.lean:103-117`), for the bridge back to manifold derivatives when needed.

**Decision criterion**: if the bundle approach is available at the pin, it wins clearly — coordinate-independence is automatic. If we have to chart-cocycle, budget extra time for the `extendCoordChange` plumbing.

Either way, pointwise `AddCommGroup` and `Module ℂ` structure on `HolomorphicOneForm X`.

Difficulty: **Medium-hard** if bundle path works (2–3 weeks). **Hard** if we have to do chart-cocycle with `extendCoordChange` (4–6 weeks including the coordinate-independence plumbing).

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

### 4.5 `RiemannSurface/IntersectionForm.lean`

Pieces Gemini 3 Pro flagged as missing from the original plan:

- **Hurewicz bridge (loops → `H_1`).** Our `H_1 X x₀ := Abelianization (FundamentalGroup X x₀)` is the classical Hurewicz theorem for connected spaces (`H_1 ≅ π_1^{ab}`), so this is definitional. But we need the explicit map `loop → H_1` to state period integration as a map from `H_1 → ℂ` (factoring through the abelianization of `π_1`).
- **Intersection pairing.** On a compact oriented surface of genus `g`, `H_1(X, ℤ)` carries a non-degenerate symplectic pairing (the intersection form). We need this to (a) state Riemann's bilinear relations (`Im τ` is positive definite *with respect to the intersection form*), (b) extract a symplectic basis `{α_i, β_j}` of `H_1`, (c) state the normalized period matrix `[I | τ]`.
- **Period injectivity.** The period map `H_1(X, ℤ) → (HolomorphicOneForm X)^∨`, `γ ↦ (ω ↦ ∫_γ ω)`, is injective for `X` of positive genus. This is a separate nontrivial fact — it's one of the Riemann bilinear relations. Axiomatize as `AX_PeriodInjective`.

```
-- Period map, restated from §4.4 but here we ask for injectivity
noncomputable def periodMap (X : Type*) [...] (x₀ : X) :
    H1 X x₀ →+ (HolomorphicOneForm X →ₗ[ℂ] ℂ) := ...

-- Axiom (discharged via Riemann bilinear in §4.4)
axiom periodMap_injective : Function.Injective (periodMap X x₀)

-- Intersection pairing
noncomputable def intersectionPairing (X : Type*) [...] (x₀ : X) :
    H1 X x₀ →+ (H1 X x₀ →+ ℤ) := ...
-- Needs orientation on X; use the complex structure to get a canonical orientation.

theorem intersectionPairing_symplectic : ...
```

Difficulty: **Medium-hard** (intersection pairing needs topology of compact oriented surfaces; Hurewicz bridge is cheap). **~2–3 weeks.**

### 4.6 `RiemannSurface/Genus.lean`

**Canonical definition.**

```
noncomputable def genus (X : Type*) [...] : ℕ :=
  Module.finrank ℂ (HolomorphicOneForm X)
```

**Crucial design constraint.** `Module.finrank` returns `0` when its module is infinite-dimensional. If `FiniteDimensional ℂ (HolomorphicOneForm X)` is only a *theorem* (not a global instance), every downstream use of `Module.finrank` can silently collapse to `0`, and the `ChartedSpace (Fin (genus X) → ℂ) (Jacobian X)` instance becomes a charted space over `Fin 0 → ℂ = Unit` — type-correct but semantically dead.

**Fix.** Install `AX_FiniteDimOneForms` as a **global instance**, not just a theorem:

```
-- In Axioms/FiniteDimOneForms.lean
axiom HolomorphicOneForm.finiteDimensional {X : Type*} [...] :
    FiniteDimensional ℂ (HolomorphicOneForm X)

-- ...then install as instance
instance : FiniteDimensional ℂ (HolomorphicOneForm X) :=
  HolomorphicOneForm.finiteDimensional
```

With this in place, `Module.finrank ℂ (HolomorphicOneForm X)` is the actual dimension, and the `ChartedSpace` instance gets a sensible model space `Fin g → ℂ`.

**No alternative "topological genus" here.** The original plan mentioned `genusTopological X := rank (H_1 X x₀) / 2` and the Hodge identity `2g = b_1`. That equivalence is Hodge theory (`dim H¹_dR = 2 dim H⁰(Ω¹)` for compact Kähler) and is not needed for the 24 sorries. Drop from this module. If the identity is needed later, it becomes a derived theorem, not an axiom.

Difficulty: **Easy** given the instance hygiene above. **~3 days.**

---

## 5. Jacobian: bridging Part A and Part B

### 5.1 `Jacobian/Construction.lean` (basis-free)

```
-- The ambient complex vector space of the Jacobian
noncomputable abbrev JacobianAmbient (X : Type*) [...] : Type :=
  HolomorphicOneForm X →ₗ[ℂ] ℂ

-- Image of H_1 under the period map (it's the lattice Λ)
noncomputable def periodLattice (X : Type*) [...] (x₀ : X) : AddSubgroup (JacobianAmbient X) :=
  AddMonoidHom.range (periodMap X x₀)

-- The Jacobian, basis-free
noncomputable def Jacobian (X : Type*) [...] (x₀ : X) : Type :=
  JacobianAmbient X ⧸ periodLattice X x₀
```

**Why basis-free.** Gemini 3 Pro correctly flagged that `Jacobian X := AbelianVariety (τ X)` makes the *type* of the Jacobian depend on an unspecified basis of `H_1` (required to construct `τ`). That leads to incoherent equivalence-class gymnastics in `pushforward`/`pullback`. The fix: the Jacobian is defined as an explicit quotient of a canonical ℂ-vector space by a canonical subgroup, no basis choice needed.

**Removing the `x₀` dependence.** The definition above depends on a choice of basepoint `x₀` through `H_1 X x₀`. Claim: `periodLattice X x₀` is **equal** (not merely isomorphic) as an `AddSubgroup` to `periodLattice X x₁` for any two basepoints `x₀, x₁`.

**Proof sketch.** `X` is path-connected (from `ConnectedSpace X` + `LocallyPathConnectedSpace X` ⇐ `ChartedSpace ℂ X`). Let `p : x₀ ⇝ x₁` be a path. For any loop `γ : [0,1] → X` based at `x₁`, the conjugated loop `p · γ · p⁻¹` is based at `x₀`. By additivity of `pathIntegral` and `pathIntegral.reverse`, `∫_{p·γ·p⁻¹} ω = ∫_p ω + ∫_γ ω - ∫_p ω = ∫_γ ω` for every `ω ∈ HolomorphicOneForm X`. So the image functional `periodMap_{x₀}(p·γ·p⁻¹) = periodMap_{x₁}(γ)` in `JacobianAmbient X`. Path-conjugation `π_1(X, x₁) → π_1(X, x₀)` is a bijection (its inverse is conjugation by `p⁻¹`), so the two period-lattice images coincide as *sets*.

**Consequence.** Define

```
-- Canonical basepoint picked via Classical choice from Nonempty X
noncomputable def Jacobian.basepoint (X : Type*) [Nonempty X] [...] : X :=
  Classical.arbitrary X

noncomputable def Jacobian (X : Type*) [Nonempty X] [...] : Type :=
  JacobianAmbient X ⧸ periodLattice X (Jacobian.basepoint X)

theorem Jacobian.periodLattice_eq_of_basepoint (x₀ x₁ : X) :
    periodLattice X x₀ = periodLattice X x₁ := ...  -- from proof sketch above
```

The lemma ensures results are independent of the specific basepoint Classical picks, even though the type `Jacobian X` is defined via one specific choice. No `iSup` gymnastics.

**Matching Buzzard's signature.** Buzzard's `Jacobian (X : Type u) [Nonempty X] [...] : Type u` takes `Nonempty X` as an instance argument. This is exactly what we need to call `Classical.arbitrary X` inside `Jacobian.basepoint`. The `Nonempty` requirement in Buzzard's signature was not accidental — it's load-bearing here.

**Instances.** The 7 instances Buzzard demands still come from Part A, but now applied to `V := JacobianAmbient X` (a finite-dim ℂ-space because `HolomorphicOneForm X` is finite-dim — which is `AX_FiniteDimOneForms`) and `Λ := periodLattice X`.

**`ChartedSpace (Fin (genus X) → ℂ) (Jacobian X)`.** Gemini 3 Pro flagged this as a dependent-type nightmare. The `ChartedSpace` instance needs an iso `Jacobian X ≃ AbelianVariety V Λ` where `V` is charted on `Fin (Module.finrank ℂ V) → ℂ` via `Basis.equivFun`. With `genus X := Module.finrank ℂ (HolomorphicOneForm X)` and a chosen basis `b`, the iso `(H⁰(X, Ω¹))^∨ ≃ (Fin (genus X) → ℂ)` is `Basis.equivFun b.dualBasis`. Plug that into the `ChartedSpace` and `IsManifold` instances. The basis choice leaks into the *instances* but not into `Jacobian X` itself — acceptable.

**`IsManifold 𝓘(ℂ) ω (Jacobian X)` vs `IsManifold (modelWithCornersSelf ℂ (Fin g → ℂ)) ω (Jacobian X)`.** Buzzard's file uses the second; his `X` uses `𝓘(ℂ)` (i.e. `modelWithCornersSelf ℂ ℂ`). These are not definitionally equal for `g ≥ 2` — the model spaces differ. Provide an explicit `IsManifold.congr` or compose with the appropriate embedding to reconcile.

Difficulty: **Medium** given Part A + Part B in place. Most of the work is the dependent-type gymnastics (`Basis.equivFun`, `IsManifold.congr`), not new mathematics. **~1–2 weeks.**

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

For holomorphic `f : X → Y` between compact Riemann surfaces, two operations on 1-forms:

1. **Pullback on forms** `f^* : HolomorphicOneForm Y → HolomorphicOneForm X`. Pointwise: `(f^* ω)_p := ω_{f(p)} ∘ df_p`. In charts, if `ω` on `Y` is locally `g(w) dw`, then `f^* ω` on `X` is locally `g(f(z)) · f'(z) dz`. No branch-locus hypothesis needed — `f^*` is unconditionally well-defined because charts pull back under composition. Linear in `ω`.

2. **Pushforward / trace on forms** `f_* : HolomorphicOneForm X → HolomorphicOneForm Y`. This requires a proper holomorphic map with finite fibers, i.e. `AX_BranchLocus`. On a regular value `q ∈ Y`, `(f_* η)_q := ∑_{p ∈ f⁻¹(q)} (η_p ∘ (df_p)⁻¹)`. At branch points, local multiplicities enter via `meromorphicOrderAt`. **`f_*` is defined only under `AX_BranchLocus`.**

**Buzzard's `pushforward` and `pullback` on Jacobians, in terms of these:**

- `pushforward f hf : Jacobian X →ₜ+ Jacobian Y`. The functoriality pattern matches **cycles**: a cycle `γ ∈ H_1(X, ℤ)` pushes forward to `f∘γ ∈ H_1(Y, ℤ)`. Dually, the period map factors through:
  `Jacobian X = (H⁰(X, Ω¹))^∨ / Λ_X → (H⁰(Y, Ω¹))^∨ / Λ_Y = Jacobian Y`
  induced by the **transpose** of `f^*` on forms: `((f^*)^T φ)(ω) := φ(f^* ω)` for `φ ∈ (H⁰(X, Ω¹))^∨`. Sends `Λ_X` into `Λ_Y` because `(f^*)^T(periodMap_X γ) = periodMap_Y (f ∘ γ)`. **Does not require `AX_BranchLocus`**.

- `pullback f hf : Jacobian Y →ₜ+ Jacobian X`. The functoriality pattern matches **forms**: a form `ω ∈ H⁰(Y, Ω¹)` pulls back to `f^* ω ∈ H⁰(X, Ω¹)`. Dually, via `f_*` on forms:
  `Jacobian Y = (H⁰(Y, Ω¹))^∨ / Λ_Y → (H⁰(X, Ω¹))^∨ / Λ_X = Jacobian X`
  induced by the **transpose** of `f_*`: `((f_*)^T φ)(ω) := φ(f_* ω)` for `φ ∈ (H⁰(Y, Ω¹))^∨`. **Requires `AX_BranchLocus`** through the definition of `f_*`.

So: `pushforward` is the easy direction (forms-pullback transposed), `pullback` is the hard direction (forms-pushforward / trace, transposed).

`ContMDiff.degree`: for `f : X → Y` non-constant holomorphic.

**Codex review correction.** The original plan led with "pick a regular value and count preimages." At the pinned commit, Sard's theorem is not in Mathlib (`Mathlib/Geometry/Manifold/WhitneyEmbedding.lean:19-24` still lists Sard as `TODO`), so the regular-value route has no foundation. The available foothold is the local meromorphic-order machinery (`Mathlib/Analysis/Meromorphic/Order.lean:39-50`, `Mathlib/Analysis/Meromorphic/Divisor.lean:36-69`).

**Revised definition via order of `f − q`**: for a non-constant holomorphic `f : X → Y` between compact Riemann surfaces and any `q : Y`, define the local degree at a point `p ∈ f⁻¹(q)` as `meromorphicOrderAt` of the difference `f − q` expressed in local charts around `p` and `q`. The global degree is the sum over `p ∈ f⁻¹(q)`:

```
def ContMDiff.degree (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) : ℕ :=
  if hconst : ∀ x y, f x = f y then 0
  else
    -- pick any q : Y (`X.Nonempty` + connected ⇒ range is nonempty)
    let q := f (Classical.arbitrary X)
    -- sum over the (finite) preimage of q
    ∑ p ∈ (f ⁻¹' {q}).toFinset,
      localOrder (f, p, q)   -- defined via meromorphicOrderAt in charts
```

For this to yield a well-defined natural number:
- **`AX_BranchLocus`** (new named axiom, stated without reference to `deg f`, see §7): asserts (a) properness, (b) discrete/finite fibers, (c) **the fiber sum `∑_{p ∈ f⁻¹(q)} localOrder(f, p, q)` is constant in `q`**, and (d) finiteness of branch locus. `ContMDiff.degree f` is then defined as that common fiber-sum value (computed at any convenient `q`, e.g. `f (Classical.arbitrary X)`).

By (c), `ContMDiff.degree f` is well-defined — it doesn't matter which `q` we pick to evaluate the sum, including critical values, because at a critical value the `localOrder`s are larger but the sum matches.

This matches the standard Riemann-surface treatment (see e.g. Forster Ch. I, Farkas–Kra).

Difficulty: **Hard** for the definitional infrastructure; **medium** once `AX_BranchLocus` is in place. **~4–6 weeks** assuming `meromorphicOrderAt` lifts cleanly to manifold-local use via charts.

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

**`⇐` direction**: `S² ≃ₜ ℂP¹`, and `H⁰(ℙ¹, Ω¹) = 0` (section of `𝒪(-2)` is always zero), so `genus S² = 0`. Independent proof using Track 2's explicit `ProjectiveLine` + `HolomorphicOneForm = 0`.

**`⇒` direction**: genus 0 ⇒ `X ≃_biholo ℂP¹` (hence homeomorphic to `S²`). Gemini 3 Pro's correction to our original plan: a **Riemann-Roch-free proof is not easier**, it requires the full Uniformization theorem (Beltrami / Dirichlet). Instead, derive genus-0 uniformization from Riemann-Roch, which is the axiom to introduce at this level.

**Proof from Riemann-Roch + Serre duality.** Let `X` compact Riemann surface, `genus X = 0`. By Riemann-Roch applied to a point divisor `D = [P]` of degree 1:
`dim H⁰(𝒪(D)) - dim H¹(𝒪(D)) = deg D + 1 - g = 1 + 1 - 0 = 2`.
Serre duality gives `dim H¹(𝒪(D)) = dim H⁰(Ω¹ ⊗ 𝒪(-D))`. For `g = 0`, `H⁰(Ω¹) = 0` (by definition of `genus`), so `H⁰(Ω¹ ⊗ 𝒪(-D)) ⊆ H⁰(Ω¹) = 0`. Hence `dim H⁰(𝒪(D)) = 2`. There exist two linearly independent meromorphic functions on `X` with at worst a simple pole at `P`; their ratio is a non-constant meromorphic function with exactly one simple pole, hence a biholomorphism `X → ℂP¹`.

**What to axiomatize.** Codex review called out that the original plan quietly used Serre duality in this proof without listing it as an axiom. Both axioms are needed:
- `AX_RiemannRoch`: `dim H⁰(𝒪(D)) - dim H¹(𝒪(D)) = deg D + 1 - g`.
- `AX_SerreDuality`: `dim H¹(𝒪(D)) = dim H⁰(Ω¹ ⊗ 𝒪(-D))` (or equivalently `H¹(𝒪(D)) ≅ H⁰(Ω¹ ⊗ 𝒪(-D))^*`).

Once both are available, the genus-0 uniformization becomes a *theorem*.

**Caveat.** Fully formalizing `H⁰` / `H¹` / line bundles on compact Riemann surfaces is significant work. For v0.1 we may further axiomatize the specific corollary "genus 0 ⇒ biholomorphic to ℙ¹" as `AX_Uniformization0`, delaying the decomposition into RR + Serre. Trade-off: cleaner v0.1 story vs. more axioms to discharge later.

Difficulty: **Medium** for `⇐`; **Medium** for `⇒` *given both axioms*; **Hard** if we want to additionally discharge both. **~3 weeks** for both directions once axioms are in place.

---

## 7. Axiomatization strategy

We tag certain deep facts as named axioms initially — this lets downstream development proceed while we stage the hard proofs.

| Axiom | Statement | True proof path | Difficulty | Instance? |
|-------|-----------|-----------------|------------|-----------|
| `AX_FiniteDimOneForms` | `FiniteDimensional ℂ (HolomorphicOneForm X)` for `X` compact Riemann surface | Compactness + normal families, or Serre duality | Hard | **Yes** (required to make `genus` well-behaved) |
| `AX_RiemannRoch` | `dim H⁰(𝒪(D)) - dim H¹(𝒪(D)) = deg D + 1 - g` | Classical | Very hard | No |
| `AX_SerreDuality` | `H¹(𝒪(D)) ≅ H⁰(Ω¹ ⊗ 𝒪(-D))^*` | Classical | Very hard | No |
| `AX_RiemannBilinear` | Period matrix is symmetric with positive-definite imaginary part | Integration by parts + Hodge star + positivity | Medium | No |
| `AX_H1FreeRank2g` | `H_1(X, ℤ)` free abelian of rank `2 · genus X` | CW / simplicial topology on compact orientable surfaces | Medium | No |
| `AX_PeriodInjective` | `periodMap : H_1(X, ℤ) → (H⁰(X, Ω¹))^∨` is injective | Consequence of `AX_RiemannBilinear` | Medium | No |
| `AX_AbelTheorem` | `0 < genus X → Function.Injective (ofCurve P₀)` | Riemann's theorem on the theta divisor, or Forster-style residue argument | Very hard | No |
| `AX_BranchLocus` | For non-constant holomorphic `f : X → Y` between compact Riemann surfaces: (a) `f` is proper, (b) every fiber `f⁻¹(q)` is discrete hence finite, (c) the sum `∑_{p ∈ f⁻¹(q)} localOrder(f, p, q)` is **independent of `q`**, (d) the set of `q` where `localOrder(f, p, q) > 1` for some `p ∈ f⁻¹(q)` is finite | Classical; uses open-map + compact-codomain | Hard | No |
| `AX_PluckerFormula` | `SmoothPlaneCurve F` with `deg F = d ≥ 3` has genus `(d-1)(d-2)/2` | Adjunction formula | Medium | No |

**Derived results (not axioms).**
- `genus_eq_zero_iff_homeo` is a *theorem* from `AX_RiemannRoch + AX_SerreDuality + AX_FiniteDimOneForms` (per §6.1). May be further axiomatized as `AX_Uniformization0` for v0.1 hygiene.
- `AX_DimOneFormsEqGenus` dropped: by defining `genus X := Module.finrank ℂ (HolomorphicOneForm X)` the equation is tautological (requires `AX_FiniteDimOneForms` as instance, per §4.6).
- The "degree is independent of regular value" statement (formerly `AX_DegreeIndependence`) is subsumed by `AX_BranchLocus`.

**Rule**: every axiom gets its own file in `Axioms/`, with a docstring stating the math, the reference (Mumford / Milne / Debarre / Forster), and why it's axiomatized. Each is a promissory note.

**Discharge priority** (order we aim to remove axioms):
1. `AX_PeriodInjective` — follows from `AX_RiemannBilinear`.
2. `AX_BranchLocus` — local `meromorphicOrderAt` + properness + connectedness; most Mathlib-ready.
3. `AX_H1FreeRank2g` — CW topology; may benefit from a future Mathlib PR on surface classification.
4. `AX_RiemannBilinear` — Hodge-theoretic identity; directly discharges `AX_PeriodInjective` and gives Jacobian ↪ `SiegelUpperHalfSpace`.
5. `AX_FiniteDimOneForms` — compactness + normal families.
6. `AX_PluckerFormula` — adjunction; Track 2 `SmoothPlaneCurve` only.
7. `AX_SerreDuality` — classical pairing; unlocks `AX_Uniformization0` with `AX_RiemannRoch`.
8. `AX_RiemannRoch` — deepest of the algebraic axioms.
9. `AX_AbelTheorem` — via `AX_RiemannRoch` + theta divisor, or Forster-style residue argument.

---

## 8. Dependency graph (critical path to closing 24 sorries)

```
Track 1 (abstract X), basis-free Jacobian:

Lattice (IsZLattice) ─────────────────────────────────────────────┐
                                                                    │
[FiniteDimensional ℂ HolomorphicOneForm] (AX_FiniteDimOneForms)    │
  ↓                                                                 │
OneForm ──→ Genus := finrank OneForm ──→ periodLattice ────────── AbelianVariety
  │                                            ↑                     │
  ↓                                            │                     ↓
PathIntegral ──→ Homology ──→ IntersectionForm ─┘                Construction ──→ 7 instances
  │                              │   │                          (basis-free: JacobianAmbient ⧸ Λ)
  │                              │   └─→ AX_PeriodInjective          │
  │                              │                                    │
  │                              └─→ (inter. pairing on H_1)          │
  │                                                                    ↓
  └────────────────────────────────────────────────────────→ AbelJacobi ──→ ofCurve, ofCurve_self
                                                                       │
                                                    AX_AbelTheorem ──→ ofCurve_inj
                                                                       │
                          AX_BranchLocus ──→ Functoriality ──→ PushPull (uses AX_BranchLocus)
                                                                       │
  AX_RiemannRoch + AX_SerreDuality ──→ Genus0 (both directions) ──────┘
                                                                       │
                                                                       ↓
                                                        all 24 sorries closed on abstract X


Track 2 (concrete X from projective embedding; depends on Part A only):

Lattice → Siegel → ComplexTorus ──────────────┐
                                                ├─→ 24 sorries closed for these concrete X:
ProjectiveCurve/Charts.lean ─┬─→ Line.lean ─────┤       ProjectiveLine, EllipticCurve-from-Weierstrass,
                             ├─→ Elliptic.lean ──┤      HyperellipticCurve g f, SmoothPlaneCurve F
                             ├─→ Hyperelliptic ──┤
                             └─→ PlaneCurve ─────┘   (AX_* discharged explicitly on these types)
```

Asterisks = axiomatizable without breaking downstream work.

**Track 1 minimum viable build**: Parts A.1–A.3 + B.1–B.5 + Jacobian/Construction.lean — closes the 7 instance sorries + `genus` on abstract `X`.

**Track 2 minimum viable build**: Parts A.1–A.3 + ProjectiveCurve/{Charts, Line, Hyperelliptic} — closes **all** 24 sorries concretely on those types, with axioms discharged. Shippable independent of Part B.

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

**Amendment note.** Original budget (~5 months to Track 1 closed-modulo-axioms) was judged "utterly unrealistic" by Gemini 3 Pro. Budget revised upward across the board, with Bochner-integration-in-Mathlib as the rough calibration (multi-person-years). The numbers below assume a Claude Code + human-expert pair-programming workflow; for fully-autonomous AI agent mode, multiply by 2–3×.

Track 1 and Track 2 run largely in parallel after Part A is done.

| Phase | Content | Est (pair) | Est (autonomous) |
|-------|---------|-----------|-------------------|
| A0 | Scaffold already done | — | — |
| A1 | `Basic.lean`, notation, test build | 1 day | 2 days |
| A2 | `Lattice.lean` + `Siegel.lean` (prefer `IsZLattice`) | 1–2 weeks | 3–4 weeks |
| A3 | `ComplexTorus.lean` — 7 instances via direct local-chart construction | 3–4 weeks | 6–10 weeks |
| A4 | `Theta.lean` — convergence, analyticity, quasi-periodicity | 4–6 weeks | 2–3 months |
| **A milestone** | **Part A standalone build, PR-able to Mathlib** | **~2 months** | **~4 months** |
| T1 | `ProjectiveCurve/Charts.lean` + `Line.lean` | 1–2 weeks | 3–4 weeks |
| T2 | `ProjectiveCurve/Elliptic.lean` (leverages Mathlib) | 2–3 weeks | 1–2 months |
| T3 | `ProjectiveCurve/Hyperelliptic.lean` — explicit atlas, 1-forms, period matrix | 8–10 weeks (+ `Complex.cpow` branch-cut pain) | 4–5 months |
| T4 | `ProjectiveCurve/PlaneCurve.lean` — implicit-function atlas, Poincaré residue basis | 8–10 weeks | 4–5 months |
| **T milestone** | **24 sorries closed concretely on ProjectiveLine + Elliptic + Hyperelliptic** | **~5 months, concurrent with B** | **~10 months** |
| B1 | `OneForm.lean` (bundle path if available; cocycle fallback) | 2–4 weeks | 2 months |
| B2 | `PathIntegral.lean` — **the big one**: chart-partition integration + homotopy invariance via Stokes on singular 2-simplices | **3 months** | **8+ months** |
| B3 | `Homology.lean` | 1–2 weeks | 1 month |
| B4 | `IntersectionForm.lean` + Hurewicz bridge | 2–3 weeks | 1–2 months |
| B5 | `Periods.lean` (axiomatize bilinear relations) | 2–3 weeks | 1–2 months |
| B6 | `Genus.lean` | 3 days | 1 week |
| **B milestone** | **`Jacobian X` defined basis-free; 7 instances close automatically on abstract X** | **~5 months after A done** | **~12 months** |
| C1 | `AbelJacobi.lean`, `Functoriality.lean` (uses branch-locus theory) | 5–6 weeks | 3–4 months |
| C2 | `PushPull.lean` — needs branch-locus + fiber integration | **2 months** (Gemini estimate: 6 months if infra greenfield) | **4–6 months** |
| C3 | `Genus0/Uniformization.lean` (⇐ direction; ⇒ via `AX_RiemannRoch`) | 3 weeks | 2 months |
| C4 | `Abel.lean` (axiomatize first) | 1 week to set up | 1 week |
| **C milestone (Track 1 challenge v0.2 closed modulo axioms)** | **~3–4 months after B done** | **~8 months** |

**Revised totals:**
- Track 2 closed concretely: **~5–6 months** (Part A + T in parallel; Hyperelliptic dominant).
- Track 1 closed modulo axioms: **~9–12 months** (A + B + C sequentially critical-path).
- Zero axioms on abstract X: **~24+ months**, dominated by `AX_RiemannRoch` and `AX_AbelTheorem`.

**Dominant costs.** `PathIntegral.lean` alone is roughly 3 months of dedicated Lean work — Gemini's analogy to Bochner integration is apt: that took multi-person-years in Mathlib. `PushPull.lean` needs branch-locus theory for holomorphic maps between compact Riemann surfaces (branch points, fiber degrees, local multiplicities), now named `AX_BranchLocus` rather than axiomatized piecemeal. `HyperellipticCurve` period integrals bleed into `Complex.cpow` branch-cut handling — the planned workaround is to parameterize cycles explicitly as arcs in the upper half plane avoiding branch points, rather than rely on `Complex.cpow`.

**v0.1 de-promise (per Codex review).** The earlier plan promised a fully worked `pushforward_pullback` genus-2 hyperelliptic example in v0.1. That requires `AX_BranchLocus` plus the fiber-sum theory that doesn't yet exist. Revised v0.1 target: the *definitional skeleton* of `pushforward`/`pullback`/`ContMDiff.degree` on `HyperellipticCurve g f`, plus explicit period-matrix computations, but `pushforward_pullback` itself left axiomatized-per-curve or deferred to v0.2.

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
- **Mathlib cotangent-bundle API turns out to be unusable** for complex manifolds at the pin. Fallback: chart-cocycle `HolomorphicOneForm`, but budget an extra month vs. the bundle path for coordinate-independence lemmas the bundle path gets for free.
- **`PathIntegral` homotopy invariance drags.** Fallback: first prove `PathIntegral (closed loop bounding a disk in a single chart) = 0` (Cauchy on ℂ), then patch together chart-local disks via Stokes on a CW structure. Axiomatize the patch-argument if it resists.
- **`Complex.cpow` branch-cut pain in `HyperellipticCurve`.** Defining explicit `α_i, β_i` cycles and integrating `x^k / √f(x)` between branch points runs into Mathlib's known difficulties around branch cuts (half-open intervals; limits across cuts not definitionally equal). Fallback: do the genus-2 case by hand first with explicit real-analytic parameterization of cycles as arcs in the upper half plane avoiding branch points; prove everything for `y² = x(x-1)(x-2)(x-3)(x-4)` as a calibration; generalize after.
- **Mumford `Sp(2g, ℤ)` action is surprisingly heavy.** We don't need this for the 24 sorries — skip for the main line.
- **Upstream Mathlib lands quotient-manifold-by-discrete-group before we do**: good for us. Re-align `ComplexTorus.lean` to use the upstream API, which will be cleaner than our direct local-chart construction.
- **Upstream lands `AddCircle` Lie-group structure (currently `TODO` at the pin)**: would give us the real-Lie-group half of the torus structure essentially for free via transport from `(AddCircle)^{2g}`. The complex structure still needs our direct construction, but the transport saves work.
- **`IsZLattice` API at the pin is incompatible with our needs.** Fallback to `FullRankLattice V` defined ad-hoc (+1 week budget).
- **Fails to build at all** on pinned Mathlib commit: fallback to a fresh Mathlib pin after `lake update`; Buzzard's file may need minor notation tweaks that he's happy to incorporate.
- **`Complex.cpow`, `Polynomial.roots`, and branch-locus theory** all turn out to be blockers beyond Hyperelliptic. Fallback: restrict Track 2 to Hyperelliptic + ProjectiveLine + Elliptic, ship the v0.1 without `PlaneCurve.lean`.

---

## 12. What we ship at v0.1

First milestone, aimed at publication / community signal. Shipped as **Track 2 + Part A + stubs for Track 1**:

1. Parts A.1–A.4 — complete standalone `AbelianVarieties` library (no sorries except optional `Theta.lean` lemmas).
2. `ProjectiveCurve/Line.lean`, `Elliptic.lean`, `Hyperelliptic.lean` — concrete projective curves satisfying all of Buzzard's typeclass constraints.
3. **All 13 data-and-instance sorries closed** (the 6 defs `genus`, `Jacobian`, `ofCurve`, `pushforward`, `pullback`, `ContMDiff.degree`, plus 7 typeclass instances) on `ProjectiveLine`, on genus-1 `EllipticCurve` examples, and on `HyperellipticCurve g f` for every squarefree `f`. Of the 11 theorem sorries, the easy ones (`ofCurve_self`, functoriality `id`/`comp` for both `pushforward` and `pullback`) are discharged on these models; the hard ones (`ofCurve_inj`, `pushforward_pullback`, holomorphicity of `ofCurve` and `push`/`pull`) are axiomatized per-curve pending `AX_BranchLocus` / `AX_AbelTheorem` / `pathIntegral` infrastructure.
4. Explicit period-matrix computations on those curves (using explicit lifted-path parameterizations, not `Complex.cpow`), with `AX_RiemannBilinear` **proved** on these models.
5. Definitions in Part B (`HolomorphicOneForm`, `pathIntegral`, `H_1`, `Jacobian X`) with signatures in place and explicit stubs; `Axioms/` populated with all nine named axioms (including `AX_SerreDuality` and `AX_BranchLocus`, both new in round 2).
6. `AX_FiniteDimOneForms` installed as a global instance, so that `genus`/`ChartedSpace` are semantically live.
7. CI green.

**Codex-review de-promise:** the earlier draft promised a *fully worked* `pushforward_pullback = deg • id` genus-2 example. That needs branch-locus infrastructure (`AX_BranchLocus` unpacked into concrete lemmas) plus fiber-sum theory that's essentially greenfield. v0.1 ships the definitional skeleton on hyperelliptic curves and per-curve axioms; the identity itself becomes a v0.2 target.

This is a substantive, defensible artifact to announce on `#Autoformalization` with honest caveats: instance sorries closed on *a rich concrete population of compact Riemann surfaces*, not on every abstract `X`; functoriality and `pushforward_pullback` axiomatized pending branch-locus infrastructure; closing the abstract case is Part B + discharging the named axioms, work in progress.

## v0.2 target

1. Part B complete — `Jacobian X` for abstract `X` works, 7 instance sorries closed on abstract `X`.
2. Axioms `AX_FiniteDimOneForms`, `AX_RiemannBilinear`, `AX_H1FreeRank2g` documented and their *statements* match Track 2 proofs exactly (a "these are the same theorem" cross-check).
3. Functoriality (`pushforward`, `pullback`, `pushforward_pullback`) closed on abstract `X` modulo `AX_BranchLocus`.
4. `genus_eq_zero_iff_homeo` (⇐ direction) closed; (⇒) depends on `AX_RiemannRoch + AX_SerreDuality + AX_FiniteDimOneForms`.

## v0.3 target

1. `AX_AbelTheorem` discharged via Riemann theta divisor on abstract `X` (needs `Theta.lean` fully in place).
2. `AX_RiemannRoch` and `AX_SerreDuality` discharged ⇒ `genus_eq_zero_iff_homeo` (⇒ direction) closed on abstract `X`.
3. `AX_RiemannExistence` — the bridge from abstract `X` to a projective model — attempted as a separate effort; if successful, Track 2 results transfer to abstract `X` automatically.
