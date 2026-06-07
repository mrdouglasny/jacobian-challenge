# Mathlib Capabilities Survey for the Jacobian Challenge

**Mathlib Baseline**: v4.29.0 (pinned in `/Users/mdouglas/Documents/GitHub/hille-yosida/.lake/packages/mathlib/`)
**Equivalence**: ~2 weeks older than target commit `8e3c989104daaa052921bf43de9eef0e1ac9fbf5` (15 April 2026)

This survey assesses what Mathlib currently provides versus what the three main construction approaches for Jacobians would require.

---

## 1. Complex Manifolds and Riemann Surfaces

**VERDICT**: PRESENT (basic setup) + PARTIAL (holomorphic structure)

### What's Present

- **Charted spaces and manifolds**: `ChartedSpace ℂ X` and `IsManifold 𝓘(ℂ) ω X` fully available
  - `/Users/mdouglas/Documents/GitHub/hille-yosida/.lake/packages/mathlib/Mathlib/Geometry/Manifold/IsManifold/Basic.lean:211-218`
    - `modelWithCornersSelf 𝕜 E` is the trivial model on a normed space
    - Notation: `𝓘(ℂ, E)` and `𝓘(ℂ)` (when E is implicit) map to `modelWithCornersSelf ℂ E`

- **Holomorphic functions on manifolds**: Basic API exists
  - `/Users/mdouglas/Documents/GitHub/hille-yosida/.lake/packages/mathlib/Mathlib/Geometry/Manifold/Complex.lean`
    - Maximum modulus principle (`Complex.norm_eventually_eq_of_mdifferentiableAt_of_isLocalMax`)
    - Liouville theorem (holomorphic → locally constant on compact spaces)
    - Integration of holomorphic differentiability is automatic via the `𝓘(ℂ)` model

- **Complex structure / conformality**:
  - `/Users/mdouglas/Documents/GitHub/hille-yosida/.lake/packages/mathlib/Mathlib/Geometry/Manifold/ConformalGroupoid.lean`
    - `conformalGroupoid` defined for conformal maps; not yet specialized to holomorphic case

- **Notation and elaborators**: Production-ready in Mathlib.Geometry.Manifold.Notation
  - `/Users/mdouglas/Documents/GitHub/hille-yosida/.lake/packages/mathlib/Mathlib/Geometry/Manifold/Notation.lean`
    - Inferential elaborators for `MDiff`, `CMDiff`, `mfderiv` etc.
    - Handles model-with-corners inference automatically (lines 341–689)

### What's Missing

- **No dedicated "Riemann surface" typeclass**: One would have to use `ChartedSpace ℂ X ∧ IsManifold 𝓘(ℂ) ω X` explicitly
  - The Buzzard challenge uses this verbose form deliberately (Challenge.lean:43-44, 47-48)
  
- **No holomorphic vector bundles/line bundles**: Only real Riemannian structure
  - Necessary for defining sheaves of holomorphic sections
  
- **No sheaves of holomorphic functions**: Not integrated with manifold API

### Ambiguous Cases

- Whether "smooth = ω-smooth" (C^∞) automatically implies holomorphic when working with 𝓘(ℂ)
  - The setup in Complex.lean confirms this holds: MDifferentiable over ℂ gives analytic functions
  - See lines 48-52, 73 of Complex.lean: uses `MDiffAt f z` to mean complex differentiable

**Conclusion**: The idiom `ChartedSpace ℂ X`, `IsManifold 𝓘(ℂ) ω X` is the right way to set up Riemann surfaces in current Mathlib.

---

## 2. Holomorphic 1-Forms / Differential Forms on Manifolds

**VERDICT**: PARTIAL (algebraic setup) + ABSENT (integration on manifolds)

### What's Present

- **Exterior algebra and exterior powers**:
  - `/Users/mdouglas/Documents/GitHub/hille-yosida/.lake/packages/mathlib/Mathlib/LinearAlgebra/ExteriorAlgebra/`
    - Basic.lean, Basis.lean, Grading.lean, OfAlternating.lean
    - Exterior algebra `⋀ M` available; grading structure exists
  
- **Analytic functions (power series)**:
  - `/Users/mdouglas/Documents/GitHub/hille-yosida/.lake/packages/mathlib/Mathlib/Analysis/Analytic/` (19 files)
    - FPowerSeries, ConvergenceRadius, Uniqueness, Composition, etc.
    - But not wrapped as "differential forms on a manifold"

### What's Missing

- **No differential forms as a bundled API**: No Ω^k(X) on a manifold
  - Exterior powers exist abstractly, but not as sections of a bundle over X
  - No integration of differential forms along paths

- **No sheaf of holomorphic 1-forms**: H⁰(X, Ω¹_X) would need both sheaves and differential forms

- **No de Rham cohomology**: H^k_dR(X) not defined
  - Singular homology/cohomology exist (AlgebraicTopology/SingularHomology/), but not de Rham variant

### Ambiguous Cases

- One could define differential forms locally via exterior algebra on each chart, then glue
  - This is not done anywhere in Mathlib yet
  - Would need careful handling of transition functions

**Conclusion**: Differential forms on manifolds are a **major gap**. Any approach using holomorphic 1-forms (e.g., computing genus via dim H⁰(X, Ω¹)) will need custom infrastructure.

---

## 3. Integration Along a Path on a Manifold

**VERDICT**: PARTIAL (for ℂ) + ABSENT (general manifolds)

### What's Present

- **Cauchy integral for functions on ℂ**:
  - `/Users/mdouglas/Documents/GitHub/hille-yosida/.lake/packages/mathlib/Mathlib/Analysis/Complex/CauchyIntegral.lean`
    - Line 18–100: Cauchy integral formula, Cauchy-Goursat, circle integrals
    - Integrals over rectangles, annuli, circles
    - Theorem: `Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable` (line ~60)

- **Path-based integration measure-theoretically**:
  - `/Users/mdouglas/Documents/GitHub/hille-yosida/.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/CircleIntegral.lean`
    - Circle integrals implemented

### What's Missing

- **No abstract line integral of 1-forms along paths on a general manifold**:
  - Works only for ℂ (or ℝ^n via divergence theorem)
  - Lifting to a Riemann surface (quotient of ℂ by a lattice) would require custom integration

- **No integration theory for sections of vector bundles**:
  - Needed to define path integrals of holomorphic 1-forms on a surface

### Ambiguous Cases

- One could potentially compose the CauchyIntegral API with a chart map to integrate on a Riemann surface locally
  - Gluing of local integrals via homotopy invariance would still be a theorem to prove

**Conclusion**: For **period lattice and Pic⁰ approaches**, line integrals of holomorphic 1-forms **must be built** (or ported from analysis texts). For **sheaf cohomology**, this is less critical (cohomology replaces explicit integration).

---

## 4. First Homology / Fundamental Group of a Compact Manifold

**VERDICT**: PRESENT (π₁ and basic homotopy groups) + PARTIAL (singular homology)

### What's Present

- **Fundamental group π₁(X, x)**:
  - `/Users/mdouglas/Documents/GitHub/hille-yosida/.lake/packages/mathlib/Mathlib/AlgebraicTopology/FundamentalGroupoid/FundamentalGroup.lean`
    - Lines 35–49: `FundamentalGroup X x` defined as automorphisms in the fundamental groupoid
    - Line 78: `map (f : C(X, Y))` induces homomorphism on fundamental groups
    - Line 54–56: Path-connected spaces have isomorphic fundamental groups at any two points

- **Higher homotopy groups π_n(X, x)**:
  - `/Users/mdouglas/Documents/GitHub/hille-yosida/.lake/packages/mathlib/Mathlib/Topology/Homotopy/HomotopyGroup.lean`
    - Lines 14–40: `π_n X x` defined via `GenLoop (Fin n) x` (functions I^n → X sending boundary to x)
    - Equivalence with path-connected components (π₀) and fundamental group (π₁)
    - Group structure for π_n (n ≥ 1), abelian for n ≥ 2

- **Singular homology**:
  - `/Users/mdouglas/Documents/GitHub/hille-yosida/.lake/packages/mathlib/Mathlib/AlgebraicTopology/SingularHomology/Basic.lean`
    - Singular complex and homology defined
    - Lines mention homotopy invariance in filename: `HomotopyInvariance.lean`, `HomotopyInvarianceTopCat.lean`

### What's Missing

- **H₁(X, ℤ) as an abelianization/first-homology group**: Abstract definition exists but
  - Not explicitly connected to π₁ (should be π₁^ab for path-connected X)
  - Not computed explicitly in any non-trivial case

- **de Rham cohomology / homology**: Not present
  - Only singular homology, which is less useful for explicit period computation

- **No reference to first Chern class or topological invariants of Riemann surfaces**:
  - 2 - 2g = χ(X) (Euler characteristic) would need integration of K (Gaussian curvature)
  - Or degree formulas via singular homology

### Ambiguous Cases

- The connection between de Rham cohomology and singular cohomology (via harmonic forms)
  - Would be needed to relate periods to Hodge theory

**Conclusion**: **π₁ is solid**, but going from π₁ to compute H₁ or genus requires either:
  1. Explicit homology computation (missing)
  2. Riemann-Roch formula or Hodge theory (not in Mathlib)

---

## 5. Divisors and Meromorphic Functions on a Riemann Surface

**VERDICT**: PRESENT (for ℂ) + PARTIAL (on manifolds)

### What's Present

- **Meromorphic functions**:
  - `/Users/mdouglas/Documents/GitHub/hille-yosida/.lake/packages/mathlib/Mathlib/Analysis/Meromorphic/Basic.lean`
    - Core definition of `MeromorphicOn f U`
  
- **Divisors of meromorphic functions**:
  - `/Users/mdouglas/Documents/GitHub/hille-yosida/.lake/packages/mathlib/Mathlib/Analysis/Meromorphic/Divisor.lean`
    - Lines 34–60: `divisor f U : Function.locallyFinsuppWithin U ℤ`
    - Maps points to their orders (valuation) at the point
    - Theorem: `divisor_apply (hf : MeromorphicOn f U) (hz : z ∈ U)` gives order at z

- **Order of a meromorphic function**:
  - `/Users/mdouglas/Documents/GitHub/hille-yosida/.lake/packages/mathlib/Mathlib/Analysis/Meromorphic/Order.lean`
    - `meromorphicOrderAt f z : ℤ ∪ ∞` (with top = ∞)

- **Additional meromorphic API**:
  - `/Users/mdouglas/Documents/GitHub/hille-yosida/.lake/packages/mathlib/Mathlib/Analysis/Meromorphic/` (8 files total)
    - FactorizedRational, NormalForm, TrailingCoefficient, Complex, IsolatedZeros, etc.

### What's Missing

- **No Picard group / Pic⁰ on a Riemann surface**:
  - Divisor classes (up to principal divisors) not formalized
  - `Pic⁰(X) = Div⁰(X) / Prin(X)` (degree-zero divisors mod principal)

- **No line bundles / divisors as invertible sheaves**:
  - Meromorphic functions are defined on ℂ or open subsets, not on abstract Riemann surfaces with charts

- **No Chow group / intersection theory**:
  - Needed for pushforward/pullback on divisors via `f_*` and `f^*`

### Ambiguous Cases

- Whether the Divisor API on ℂ lifts cleanly to a Riemann surface via sheaf-theoretic pushforward
  - No evidence this path is taken in Mathlib

**Conclusion**: **Divisors and meromorphic functions work on ℂ**, but not as a geometric object on a Riemann surface manifold. The **Pic⁰ approach** would need:
  1. Divisor class group formalization
  2. Jacobian as a quotient (manifold structure on Div⁰ / Prin)
  3. Abel-Jacobi map into Jacobian

---

## 6. Sheaf Cohomology on Complex Manifolds

**VERDICT**: PRESENT (abstract sheaf cohomology) + ABSENT (on analytic sites)

### What's Present

- **Abstract sheaf cohomology**:
  - `/Users/mdouglas/Documents/GitHub/hille-yosida/.lake/packages/mathlib/Mathlib/CategoryTheory/Sites/SheafCohomology/Basic.lean`
    - Lines 57–59: `Sheaf.H F n : Type` = Ext-group from constant sheaf ℤ to F
    - Lines 90–107: `Sheaf.cohomologyPresheaf F n` (presheaf of H^n sections over opens)
    - General framework with `HasExt` and derived functors

- **Cech cohomology**:
  - `/Users/mdouglas/Documents/GitHub/hille-yosida/.lake/packages/mathlib/Mathlib/CategoryTheory/Sites/SheafCohomology/Cech.lean`
    - Cech complex defined

- **Mayer-Vietoris**:
  - `/Users/mdouglas/Documents/GitHub/hille-yosida/.lake/packages/mathlib/Mathlib/CategoryTheory/Sites/SheafCohomology/MayerVietoris.lean`
    - Long exact sequence in cohomology

- **Sheaf foundations**:
  - `/Users/mdouglas/Documents/GitHub/hille-yosida/.lake/packages/mathlib/Mathlib/Topology/Sheaves/Sheaf.lean`
    - Sheaves over a topological space, sheafification

### What's Missing

- **No analytic site**: SheafCohomology works with general Grothendieck topologies, but
  - Not specialized to the analytic topology on ℂ^n or a Riemann surface
  - No "holomorphic functions" as a sheaf instance

- **No Hodge theory**: Cohomology is abstract; no Dolbeault or Hodge diamond

- **No Serre duality**: H^k(X, L) ≃ H^{n-k}(X, K ⊗ L^{-1})* for line bundles on curves

- **No computable examples**: Sheaf cohomology theorems exist but no example computations

### Ambiguous Cases

- Can one instantiate `Sheaf J (AddCommGrpCat)` with J = analytic topology and compute H^0(X, Ω¹)?
  - Theoretically possible but untested; requires building the analytic topology and coherent sheaves

**Conclusion**: Mathlib has **solid abstract sheaf cohomology**, but the **sheaf cohomology approach** would require:
  1. Defining a sheaf of holomorphic functions on a Riemann surface
  2. Constructing the sheaf Ω¹ of holomorphic 1-forms
  3. Computing H⁰(X, Ω¹) and using Riemann-Roch
  4. All custom work on top of Mathlib's abstract framework

---

## 7. Quotient of a Manifold by a Discrete Group Action

**VERDICT**: ABSENT (manifold instance for quotient)

### What's Present

- **Group actions and quotients (general)**:
  - `/Users/mdouglas/Documents/GitHub/hille-yosida/.lake/packages/mathlib/Mathlib/GroupTheory/GroupAction/Quotient.lean`
    - `QuotientGroup.instQuotientAction` and quotient maps

- **Discrete quotients topologically**:
  - `/Users/mdouglas/Documents/GitHub/hille-yosida/.lake/packages/mathlib/Mathlib/Topology/DiscreteQuotient.lean`
    - DiscreteQuotient as a concept

- **Open quotient maps**:
  - `/Users/mdouglas/Documents/GitHub/hille-yosida/.lake/packages/mathlib/Mathlib/Topology/Maps/OpenQuotient.lean`
    - Open quotient topology for open maps

### What's Missing

- **Charted space instance on X/G for X a manifold and G discrete**:
  - The Buzzard challenge references an open Zulip discussion by Michael Rothgang
  - As of this survey date, **no manifold instance** is in Mathlib
  - Status: "charted-space instance in review; manifold instance sorry-free modulo smooth Lie group action"

- **Smooth action of discrete group on manifold**:
  - Not formalized

### Implications for Jacobian

- **Period lattice approach (ℂ^g / Λ)**: 
  - Λ ⊂ ℂ^g is a discrete subgroup (rank 2g)
  - Quotient ℂ^g / Λ must have a manifold structure
  - **Currently must be built manually** (define charts, gluing)

- **Pic⁰ approach**: Depends on above if Pic⁰ is realized as a quotient

**Conclusion**: **Critical gap**. No off-the-shelf manifold quotient by discrete group. Must define quotient charts manually or wait for the Rothgang fix to land.

---

## 8. ContMDiff.degree of a Map Between Manifolds

**VERDICT**: ABSENT

### What's Sought

The Buzzard challenge requires:
```lean
def _root_.ContMDiff.degree (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) : ℕ
```
Maps between compact Riemann surfaces with a well-defined topological degree.

### What's Present

- **Topological degree for maps ℝ^n → ℝ^n**: Not found in search results
  - Singular homology exists but no "degree of map" instantiation
  
- **Brouwer degree**: Not implemented

### What Would Be Needed

1. Define `H_1(X, ℤ)` for compact connected 1-dimensional complex manifolds
2. Compute the induced homomorphism `f_* : H_1(X, ℤ) → H_1(Y, ℤ)`
3. Define degree = determinant of this map (in the rank-1 case)
4. Or use the residue formula for meromorphic differentials

### Conclusion

**Completely absent**. Any construction relying on `ContMDiff.degree` (pullback/pushforward compatibility, `degree • P` in the Jacobian) must be custom-built.

---

## 9. Uniformization / Classification of Genus-0 Riemann Surfaces

**VERDICT**: ABSENT

### What's Sought

`genus_eq_zero_iff_homeo : genus X = 0 ↔ Nonempty (X ≃ₜ Metric.sphere (0 : ℝ^3) 1)`

### What's Present

- **Sphere manifold structure**:
  - `/Users/mdouglas/Documents/GitHub/hille-yosida/.lake/packages/mathlib/Mathlib/Geometry/Manifold/Instances/Sphere.lean`
    - Stereographic projection, analytic manifold on sphere
    - Circle (S¹) as a Lie group

- **Analytic maps**:
  - CauchyIntegral shows basic complex analysis (Liouville theorem, maximum modulus)

### What's Missing

- **No topological classification of surfaces**:
  - Would need the classification theorem or genus definition itself
  - The Buzzard challenge defines genus via a sorry, so this is not a critical blocker
  - But **proving** `genus_eq_zero_iff_homeo` requires deep topological machinery

- **No uniformization theorem**: "Every genus-0 compact Riemann surface is ℂℙ¹"
  - This is a major theorem; would need analytic continuation, moduli spaces, etc.

### Conclusion

**Completely absent**. Buzzard's challenge makes `genus_eq_zero_iff_homeo` a sorry, implying this is **not expected to be proven** in the challenge. Use of Riemann surfaces of arbitrary genus proceeds without this uniformization fact (only needed for explicit genus-0 examples).

---

## 10. Notation Check: 𝓘(ℂ, E) vs modelWithCornersSelf ℂ E

**VERDICT**: EQUIVALENT (notation is syntax sugar)

### Finding

- **Definition**:
  - `/Users/mdouglas/Documents/GitHub/hille-yosida/.lake/packages/mathlib/Mathlib/Geometry/Manifold/IsManifold/Basic.lean:215`
    ```lean
    scoped[Manifold] notation "𝓘(" 𝕜 ", " E ")" => modelWithCornersSelf 𝕜 E
    ```
  - Line 218: `𝓘(𝕜)` := `modelWithCornersSelf 𝕜 𝕜`

- **Usage in Buzzard**:
  - Challenge.lean:44 uses `𝓘(ℂ)` 
  - Challenge.lean:83 uses `modelWithCornersSelf ℂ (Fin (genus X) → ℂ)` 

Both are **identical** after elaboration. The notation is purely syntactic sugar for readability.

### Conclusion

Use `𝓘(ℂ)` and `𝓘(ℂ, E)` freely. Mathlib's elaborators handle the notation correctly at v4.29.0.

---

## Summary Table

| Topic | Status | Key File(s) | Verdict |
|-------|--------|-----------|---------|
| Complex manifolds (𝓘(ℂ) setup) | PRESENT | Geometry/Manifold/IsManifold/Basic.lean:211-218 | ✓ Ready |
| Holomorphic functions | PRESENT | Geometry/Manifold/Complex.lean | ✓ Ready |
| Differential forms on manifolds | ABSENT | - | ✗ Missing |
| Line integrals on manifolds | ABSENT (general) | Analysis/Complex/CauchyIntegral.lean (ℂ only) | ⚠ Partial |
| π₁ fundamental group | PRESENT | AlgebraicTopology/FundamentalGroupoid/FundamentalGroup.lean | ✓ Ready |
| Singular homology | PRESENT | AlgebraicTopology/SingularHomology/Basic.lean | ✓ Ready |
| Meromorphic functions & divisors | PRESENT (ℂ) | Analysis/Meromorphic/Divisor.lean | ✓ Ready (ℂ only) |
| Sheaf cohomology (abstract) | PRESENT | CategoryTheory/Sites/SheafCohomology/Basic.lean | ✓ Ready |
| Sheaf of holomorphic functions | ABSENT | - | ✗ Missing |
| Quotient manifold by discrete group | ABSENT | - | ✗ Missing |
| Mapping degree (ContMDiff.degree) | ABSENT | - | ✗ Missing |
| Genus definition / uniformization | ABSENT | - | ✗ Missing |
| 𝓘(ℂ, E) notation | PRESENT | Geometry/Manifold/IsManifold/Basic.lean:215 | ✓ Ready |

---

## Construction Strategy Implications

### Approach A: Period Lattice (ℂ^g / Λ)

**Feasibility**: ⚠ **DIFFICULT**

**Blockers**:
1. **Quotient manifold by discrete group** (ABSENT) — must build manually
   - Define charts on ℂ^g / Λ using fundamental domain
   - Prove manifold axioms
   
2. **Computing periods** (PARTIAL)
   - Line integrals of holomorphic 1-forms on a Riemann surface not in Mathlib
   - Must build: integrate α ∈ H⁰(X, Ω¹) along γ ∈ H₁(X, ℤ)
   - Then compute the period lattice Λ = {∫_γ α : γ ∈ H₁(X, ℤ), α ∈ H⁰(X, Ω¹)}

3. **Dimension**: Must prove dim H⁰(X, Ω¹) = genus
   - Requires Riemann-Roch theorem or Hodge theory — not in Mathlib

**Advantages**:
- Explicit geometric model (ℂ^g / Λ is concrete)
- Jacobian naturally an abelian variety

**Custom work required**: ~40% of construction from scratch

---

### Approach B: Picard Group (Pic⁰(X) = Div⁰(X) / Prin(X))

**Feasibility**: ⚠ **DIFFICULT**

**Blockers**:
1. **Divisor class group** (ABSENT)
   - Meromorphic divisors on Riemann surfaces not formalized
   - Must define: degrees of divisors, principal divisors, equivalence classes
   - Line 38 of Meromorphic/Divisor.lean shows divisors on ℂ, but these don't glue to manifolds

2. **Manifold structure on quotient** (ABSENT)
   - Pic⁰(X) is a quotient of an abelian group; needs manifold instance
   - Depends on solving the discrete group action problem

3. **Functoriality** (ABSENT)
   - Pushforward/pullback of divisor classes under holomorphic maps

**Advantages**:
- Conceptually clean: Pic⁰ is intrinsically defined
- Naturally a complex torus

**Custom work required**: ~50% of construction from scratch

---

### Approach C: Sheaf Cohomology (H⁰(X, Ω¹) → Pic⁰ via Dolbeault)

**Feasibility**: ⚠ **DIFFICULT (but most aligned with Mathlib)**

**Blockers**:
1. **Sheaf of holomorphic functions** (ABSENT)
   - Mathlib has abstract sheaves and sheaf cohomology
   - No instantiation with "analytic topology" or holomorphic functions

2. **Holomorphic 1-forms** (ABSENT)
   - No Ω¹ sheaf or differential forms on manifolds
   - Must define bundles and sections

3. **Dolbeault cohomology** (ABSENT)
   - Relies on ∂̄ operator on (0,1)-forms
   - Not in Mathlib

4. **Comparison with singular homology** (ABSENT)
   - H^k(X, ℤ) ≅ H^k_singular(X, ℤ) not formalized

**Advantages**:
- Mathlib's sheaf cohomology is well-built (abstract layer is strong)
- Once sheaves are set up, `Sheaf.H` gives cohomology automatically
- Could leverage existing cohomology machinery (Mayer-Vietoris, etc.)

**Custom work required**: ~60% of construction, but on well-structured ground

---

## Recommendation

Given the landscape:

1. **Genus definition**: Buzzard's challenge already makes this a `sorry`. No penalty for using a non-constructive definition (e.g., via Riemann-Roch or topological invariant).

2. **If feasible in timeline, choose Period Lattice**:
   - Simplest geometry to formalize
   - Explicit ℂ^g / Λ is concrete
   - Avoid deep categorical machinery
   - Main work: manifold quotient + period integrals

3. **If time is unlimited and community support available, sheaf cohomology**:
   - Most aligned with Mathlib's abstract structure
   - Reusable for other complex geometry
   - But requires building differential forms infrastructure

4. **Avoid Pic⁰ unless mandatory**:
   - Combines gaps from both A and B
   - No advantage over period lattice
   - Requires divisor class quotient (harder than ℂ^g / Λ)

5. **For `ContMDiff.degree`**:
   - Compute via Bezout / residue formula on meromorphic differentials
   - Or use singular homology + degree from H₁
   - Both require custom work either way

---

## Files Checklist for Further Investigation

### Core References
- ✓ `/Users/mdouglas/Documents/GitHub/hille-yosida/.lake/packages/mathlib/Mathlib/Geometry/Manifold/`
  - IsManifold/Basic.lean (notations, models)
  - Complex.lean (holomorphic functions)
  - ConformalGroupoid.lean (conformal structure)

- ✓ `/Users/mdouglas/Documents/GitHub/hille-yosida/.lake/packages/mathlib/Mathlib/Analysis/Complex/`
  - CauchyIntegral.lean (line integrals on ℂ)

- ✓ `/Users/mdouglas/Documents/GitHub/hille-yosida/.lake/packages/mathlib/Mathlib/Analysis/Meromorphic/`
  - Divisor.lean (divisors on ℂ)
  - Order.lean (valuation of meromorphic functions)

- ✓ `/Users/mdouglas/Documents/GitHub/hille-yosida/.lake/packages/mathlib/Mathlib/AlgebraicTopology/`
  - FundamentalGroupoid/FundamentalGroup.lean
  - SingularHomology/Basic.lean

- ✓ `/Users/mdouglas/Documents/GitHub/hille-yosida/.lake/packages/mathlib/Mathlib/CategoryTheory/Sites/SheafCohomology/`
  - Basic.lean (abstract sheaf cohomology)

- ⚠ Missing: Differential forms, Picard group, quotient manifolds, mapping degree, genus

