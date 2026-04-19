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
- Part B depends on Mathlib (no differential forms on manifolds, per Phase B) plus `Axioms/`.
- `Jacobian/` is pure glue: take `τ(X)` from Part B, feed to Part A, get all instances for free.

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
                                                                                    
                                                                                    └→ all 22 sorries closed
```

Asterisks = axiomatizable without breaking downstream work.

Minimum viable build: Parts A.1–A.3 + B.1–B.5 + Jacobian/Construction.lean — closes the 7 instance sorries + `genus`.

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

| Phase | Content | Est |
|-------|---------|-----|
| A0 | Scaffold already done | — |
| A1 | `Basic.lean`, notation, test build | 1 day |
| A2 | `Lattice.lean` + `Siegel.lean` | 1 week |
| A3 | `ComplexTorus.lean` — all 7 instances | 2–3 weeks |
| A4 | `Theta.lean` — convergence + quasi-periodicity (optional for sorries) | 2 weeks |
| **A milestone** | **Part A standalone build, PR-able as Mathlib contribution** | **~5 weeks** |
| B1 | `OneForm.lean` | 1–2 weeks |
| B2 | `PathIntegral.lean` — this is the hard one | 3–6 weeks |
| B3 | `Homology.lean` | 1 week |
| B4 | `Periods.lean` (axiomatize bilinear relations) | 1–2 weeks |
| B5 | `Genus.lean` | 3 days |
| **B milestone** | **`Jacobian X` defined and 7 instances close automatically** | **~9 weeks after A done** |
| C1 | `AbelJacobi.lean`, `Functoriality.lean` | 3–4 weeks |
| C2 | `PushPull.lean` | 2 weeks |
| C3 | `Genus0/Uniformization.lean` (⇐ direction) | 2 weeks |
| C4 | `Abel.lean` (axiomatize first) | 1 week to set up, months to discharge |
| **C milestone (challenge v0.2 closed modulo axioms)** | **~7 weeks after B done** |

Total to "closed modulo axioms": **~5 months**, conservatively. To "zero axioms": significantly longer (12+ months), dominated by Abel's theorem via theta divisor + uniformization for genus 0.

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

First milestone, aimed at publication / community signal:
1. Parts A.1–A.4 — complete standalone `AbelianVarieties` library, no sorries (except optional Theta.lean lemmas).
2. Definitions in Part B, signatures in place, `Axioms/` set up.
3. `Jacobian X` defined; 7 instance sorries closed.
4. `ofCurve` defined; `ofCurve_self` proved.
5. Genus-1 special case worked out explicitly as an example file.
6. CI green.

This is a legitimate artifact to announce back on Lean Zulip, with honest caveats about what's axiomatized.
